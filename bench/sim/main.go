// sim 是内核之外的独立评测台：用与 LaminaDB 引擎同构的内存结构，
// 复刻三种唯一约束维护方向，在同一可复现负载上比较状态、校验工作与恢复责任。
// 它不 import internal/，也不修改内核，只模拟 engine/constraints.go 的语义。
package main

import (
	"flag"
	"fmt"
	"math/rand"
	"os"
	"runtime"
	"sort"
	"strings"
	"time"
)

// ---- 与 datum.Value.Key() 同构的 token ----
func intKey(n int64) string  { return fmt.Sprintf("int:%d", n) }
func textKey(s string) string { return "text:" + quote(s) }
func quote(s string) string {
	b := &strings.Builder{}
	b.WriteByte('"')
	for _, r := range s {
		switch r {
		case '"':
			b.WriteString(`\"`)
		case '\\':
			b.WriteString(`\\`)
		default:
			b.WriteRune(r)
		}
	}
	b.WriteByte('"')
	return b.String()
}

// Row 是引擎一行的简化：主键 -> 唯一列 token（null 用空串表示，跳过）。
type Row struct {
	key   string
	uniq  string // 唯一列 token；空串 = null（多个 null 允许）
}

// Mutation 对应 versions.Mutation。
type Mutation struct {
	key    string
	row    Row
	delete bool
}

// Store 对应 versions.Store 的可见语义：每键一条版本链，Scan 取 at 水位可见行。
type version struct {
	seq     uint64
	row     Row
	deleted bool
}
type Store struct {
	chains map[string][]version
	seq    uint64
}

func newStore() *Store { return &Store{chains: map[string][]version{}} }

func (s *Store) apply(writes []Mutation) {
	s.seq++
	for _, m := range writes {
		s.chains[m.key] = append(s.chains[m.key], version{seq: s.seq, row: m.row, deleted: m.delete})
	}
}

// Scan 复刻 versions.Store.Scan：取每条链在当前水位的可见（非墓碑）行。
func (s *Store) Scan() map[string]Row {
	out := map[string]Row{}
	for k, chain := range s.chains {
		last := chain[len(chain)-1]
		if !last.deleted {
			out[k] = last.row
		}
	}
	return out
}

// ---- 历史候选树，复刻 index.Tree：保留全部历史 (value,key)，去重，有序切片 ----
type histEntry struct{ token, key string }
type histTree struct {
	entries []histEntry
	seen    map[string]bool
}

func newHistTree() *histTree { return &histTree{seen: map[string]bool{}} }
func (t *histTree) add(token, key string) {
	if token == "" {
		return
	}
	combo := token + "\x00" + key
	if t.seen[combo] {
		return
	}
	t.seen[combo] = true
	at := sort.Search(len(t.entries), func(i int) bool {
		e := t.entries[i]
		return e.token > token || (e.token == token && e.key >= key)
	})
	t.entries = append(t.entries, histEntry{})
	copy(t.entries[at+1:], t.entries[at:])
	t.entries[at] = histEntry{token, key}
}
func (t *histTree) size() int { return len(t.entries) }

// 方向 A：基线。每次提交 Scan 全关系 + overlay，再对全量可见行重建临时 set。
type DirectionA struct {
	store *Store
	// 统计量
	rowsScanned  int64 // 进入唯一校验的可见行数（含 overlay）
	tmpSetsAlloc int64 // 每次提交一个临时 map 的分配次数
	tmpMapInserts int64
}

func newA() *DirectionA { return &DirectionA{store: newStore()} }

// check 复刻 engine.unique + checkUnique：先全量 Scan，再 overlay，再全表建 set。
func (a *DirectionA) check(writes []Mutation) error {
	rows := a.store.Scan()
	for _, m := range writes {
		if m.delete {
			delete(rows, m.key)
		} else {
			rows[m.key] = m.row
		}
	}
	a.rowsScanned += int64(len(rows))
	a.tmpSetsAlloc++
	values := map[string]string{}
	for key, row := range rows {
		if row.uniq == "" {
			continue
		}
		a.tmpMapInserts++
		if prior, ok := values[row.uniq]; ok && prior != key {
			return fmt.Errorf("unique violated")
		}
		values[row.uniq] = key
	}
	return nil
}
func (a *DirectionA) commit(writes []Mutation) error {
	if err := a.check(writes); err != nil {
		return err
	}
	a.store.apply(writes)
	return nil
}

// 方向 B：常驻“当前态” token->owner 映射，提交时只触碰写集。
type DirectionB struct {
	store *Store
	owner map[string]string // 当前可见唯一值 -> 持有它的主键；null 不入表
	// 统计量
	touchedLookups int64
	mapUpdates     int64
}

func newB() *DirectionB {
	return &DirectionB{store: newStore(), owner: map[string]string{}}
}

// check 只看写集相关的键与值：从 store 当前可见态出发，叠加写集得到受影响键的
// “最终值”，再判定每个最终非空值的归属是否唯一。
// 关键：以最终关系状态为准，因此同一事务内 A<->B 的合法置换不会误判，
// 历史上用过、现已释放的值也不会被永久占用。
func (b *DirectionB) check(writes []Mutation) error {
	// 受影响键：写集中的键，加上当前持有“写集目标值”的外部键。
	keys := map[string]bool{}
	newTokByKey := map[string]string{} // 写集键的最终值（删除为空）
	for _, m := range writes {
		keys[m.key] = true
		if m.delete {
			newTokByKey[m.key] = ""
		} else {
			newTokByKey[m.key] = m.row.uniq
		}
	}
	// 当前可见态 helper
	live := func(k string) string {
		chain, ok := b.store.chains[k]
		if !ok {
			return ""
		}
		last := chain[len(chain)-1]
		if last.deleted {
			return ""
		}
		return last.row.uniq
	}
	// 把外部持有者也纳入受影响集合。
	for _, tok := range newTokByKey {
		if tok == "" {
			continue
		}
		b.touchedLookups++
		if holder, occupied := b.owner[tok]; occupied && !keys[holder] {
			keys[holder] = true
		}
	}
	// 计算每个受影响键的最终值并做唯一性判定。
	final := map[string]string{}
	for k := range keys {
		if nv, written := newTokByKey[k]; written {
			final[k] = nv
		} else {
			final[k] = live(k)
		}
	}
	holderOf := map[string]string{}
	for k, tok := range final {
		if tok == "" {
			continue
		}
		if other, dup := holderOf[tok]; dup && other != k {
			return fmt.Errorf("unique violated")
		}
		holderOf[tok] = k
	}
	return nil
}

// applyMap 在提交成功后把常驻 owner 推进到最终态。
func (b *DirectionB) applyMap(writes []Mutation) {
	// 重算受影响键的旧值并摘除，再登记新值。
	oldByKey := map[string]string{}
	for _, m := range writes {
		if chain, ok := b.store.chains[m.key]; ok {
			last := chain[len(chain)-1]
			if !last.deleted {
				oldByKey[m.key] = last.row.uniq
			}
		}
	}
	// 摘除：仅当该旧值确实仍由该键持有时。
	for key, tok := range oldByKey {
		if tok != "" && b.owner[tok] == key {
			delete(b.owner, tok)
			b.mapUpdates++
		}
	}
	for _, m := range writes {
		if m.delete || m.row.uniq == "" {
			continue
		}
		b.owner[m.row.uniq] = m.key
		b.mapUpdates++
	}
}
func (b *DirectionB) commit(writes []Mutation) error {
	if err := b.check(writes); err != nil {
		return err
	}
	b.store.apply(writes)
	b.applyMap(writes)
	return nil
}

// rebuild 是恢复责任：从最终 store 全量重建常驻 owner（WAL/镜像仍是唯一事实源）。
func (b *DirectionB) rebuild() (entries int) {
	owner := map[string]string{}
	for key, chain := range b.store.chains {
		last := chain[len(chain)-1]
		if last.deleted || last.row.uniq == "" {
			continue
		}
		if prior, dup := owner[last.row.uniq]; dup && prior != key {
			panic("rebuild found unique violation") // 恢复校验应拒绝这种状态
		}
		owner[last.row.uniq] = key
		entries++
	}
	b.owner = owner
	return entries
}

// 方向 C：复用现有历史候选树做提交点查。注意树保留全部历史候选。
type DirectionC struct {
	store *Store
	tree  *histTree
	// 统计量
	candidateProbes int64
	candidateRows   int64
}

func newC() *DirectionC { return &DirectionC{store: newStore(), tree: newHistTree()} }

// check：对写集每个新值，在历史树里取等值候选键，再回版本链判活 + overlay。
// 不做全表 Scan。候选数随历史版本增长（树保留全部历史 (value,key)），是 C 的主要成本。
func (c *DirectionC) check(writes []Mutation) error {
	// 写集最终态：key -> 新 token（删除则不在表中）
	overlay := map[string]string{}
	deleted := map[string]bool{}
	for _, m := range writes {
		if m.delete {
			deleted[m.key] = true
			delete(overlay, m.key)
		} else {
			overlay[m.key] = m.row.uniq
		}
	}
	probed := map[string]bool{}
	for _, m := range writes {
		if m.delete || m.row.uniq == "" || probed[m.row.uniq] {
			continue
		}
		probed[m.row.uniq] = true
		c.candidateProbes++
		// 树中等值范围的全部历史候选键
		lo := sort.Search(len(c.tree.entries), func(i int) bool { return c.tree.entries[i].token >= m.row.uniq })
		hi := lo
		for hi < len(c.tree.entries) && c.tree.entries[hi].token == m.row.uniq {
			hi++
		}
		// 每个候选键回 versions 判当前可见值，再叠加 overlay，判断最终是否仍占该值。
		for _, e := range c.tree.entries[lo:hi] {
			c.candidateRows++
			candKey := e.key
			tok := ""
			if chain, ok := c.store.chains[candKey]; ok {
				last := chain[len(chain)-1]
				if !last.deleted {
					tok = last.row.uniq
				}
			}
			if ov, ok := overlay[candKey]; ok {
				tok = ov
			}
			if deleted[candKey] {
				tok = ""
			}
			// 该候选键在最终态仍持有目标值，且不是本次写这个值的键 -> 真冲突。
			if tok == m.row.uniq && candKey != m.key {
				return fmt.Errorf("unique violated")
			}
		}
		// 写集内两个键写同值（可能是尚未进树的全新键/新值）也要拦截。
		for k, tok := range overlay {
			if tok == m.row.uniq && k != m.key {
				return fmt.Errorf("unique violated")
			}
		}
	}
	return nil
}
func (c *DirectionC) commit(writes []Mutation) error {
	if err := c.check(writes); err != nil {
		return err
	}
	c.store.apply(writes)
	for _, m := range writes {
		if !m.delete {
			c.tree.add(m.row.uniq, m.key)
		}
	}
	return nil
}

// ---- 负载生成：可复现。稳态负载绝大多数合法（不制造意外冲突）；
//      置换、历史值复用、真冲突三类语义由 correctness() 专门验证。 ----
type workload struct {
	name    string
	keys    int  // 关系规模 N
	domain  int  // 唯一值域大小
	commits int  // 提交数
	batch   int  // 每提交写集大小 w
	seed    int64
	text    bool
	swap    bool // true=固定域内轮换（置换/复用密集）；false=增长域
}

func (wl workload) token(v int64) string {
	if wl.text {
		return textKey(fmt.Sprintf("tag-%08d", v))
	}
	return intKey(v)
}

// gen 生成一串“预期合法”的提交。维护 owner 反查表，保证每批选中的值互不相同，
// 且不被写集之外的键持有——从而这些提交在正确的唯一约束下必须被接受。
func (wl workload) gen() [][]Mutation {
	rng := rand.New(rand.NewSource(wl.seed))
	current := map[string]int64{} // key -> 当前值
	owner := map[int64]string{}   // value -> 当前持有 key
	for k := 0; k < wl.keys; k++ {
		key := fmt.Sprintf("int:%d", int64(k+1))
		current[key] = int64(k)
		owner[int64(k)] = key
	}
	commits := make([][]Mutation, 0, wl.commits)
	nextFree := int64(wl.keys) // 增长域下一个未用过的值
	for c := 0; c < wl.commits; c++ {
		// 选 w 个不同的键
		perm := rng.Perm(wl.keys)
		chosenKeys := make([]string, 0, wl.batch)
		for i := 0; i < wl.batch && i < len(perm); i++ {
			chosenKeys = append(chosenKeys, fmt.Sprintf("int:%d", int64(perm[i]+1)))
		}
		var muts []Mutation
		if wl.swap {
			// 构造性合法置换：对选中键的“当前值集合”做循环移位（双射）。
			// 每个新值都来自写集内部、且一一对应，因此必然满足唯一约束，
			// 同时密集触发“同事务值置换 + 历史值复用”。
			vals := make([]int64, len(chosenKeys))
			for i, k := range chosenKeys {
				vals[i] = current[k]
			}
			shift := 1 + rng.Intn(len(vals)-1)
			if len(vals) == 1 {
				shift = 0
			}
			for i, k := range chosenKeys {
				nv := vals[(i+shift)%len(vals)]
				if nv == current[k] {
					continue
				}
				muts = append(muts, Mutation{key: k, row: Row{key: k, uniq: wl.token(nv)}})
			}
		} else {
			// 增长域：用 owner 账本挑合法值，75% 取全新值，25% 复用可释放的值。
			keySet := map[string]bool{}
			for _, k := range chosenKeys {
				keySet[k] = true
			}
			usedVals := map[int64]bool{}
			muts = make([]Mutation, 0, wl.batch)
			for _, key := range chosenKeys {
				old := current[key]
				var nv int64
				for attempt := 0; ; attempt++ {
					if attempt == 0 && rng.Intn(4) != 0 && nextFree < int64(wl.domain) {
						nv = nextFree
						nextFree++
					} else {
						nv = int64(rng.Intn(wl.domain))
					}
					if nv == old || usedVals[nv] {
						if attempt > 64 {
							nv = old
							break
						}
						continue
					}
					if holder, occupied := owner[nv]; occupied && !keySet[holder] {
						if attempt > 64 {
							nv = old
							break
						}
						continue
					}
					break
				}
				if nv == old {
					continue
				}
				usedVals[nv] = true
				muts = append(muts, Mutation{key: key, row: Row{key: key, uniq: wl.token(nv)}})
			}
		}
		// 把这一批真正应用到生成器的账本上
		for _, m := range muts {
			old := current[m.key]
			delete(owner, old)
			var nv int64
			if wl.text {
				fmt.Sscanf(m.row.uniq, "text:\"tag-%08d\"", &nv)
			} else {
				fmt.Sscanf(m.row.uniq, "int:%d", &nv)
			}
			current[m.key] = nv
			owner[nv] = m.key
		}
		if len(muts) > 0 {
			commits = append(commits, muts)
		}
	}
	return commits
}

// seedStore 建立初始 N 行（每个 key 一个互不相同的唯一值）。
func seedStore(s *Store, wl workload) {
	muts := make([]Mutation, 0, wl.keys)
	for k := 0; k < wl.keys; k++ {
		key := fmt.Sprintf("int:%d", int64(k+1))
		muts = append(muts, Mutation{key: key, row: Row{key: key, uniq: wl.token(int64(k))}})
	}
	// 分块应用以贴近真实多提交
	chunk := 500
	for i := 0; i < len(muts); i += chunk {
		end := i + chunk
		if end > len(muts) {
			end = len(muts)
		}
		s.apply(muts[i:end])
	}
}

type result struct {
	dir            string
	elapsed        time.Duration
	conflicts      int
	commitsOK      int
	rowsScanned    int64
	lookups        int64
	candidateRows  int64
	histEntries    int
	residentBytes  uint64
	rebuildElapsed time.Duration
	rebuildEntries int
}

func memOf(x any) uint64 {
	var m1, m2 runtime.MemStats
	runtime.GC()
	runtime.ReadMemStats(&m1)
	runtime.KeepAlive(x)
	runtime.GC()
	runtime.ReadMemStats(&m2)
	return m2.HeapAlloc
}

// correctness 验证三类语义在 A/B/C 上判定完全一致：
//  1. 同一事务内两个键合法置换唯一值（必须接受）
//  2. 一个值被释放后，后续提交复用它（必须接受，不能永久占用）
//  3. 两个不同键抢同一仍被占用的值（必须拒绝）
//  4. null 多个允许
func correctness() {
	type tc struct {
		name      string
		seed      []Mutation // 初始数据（已视为合法）
		commit    []Mutation
		wantError bool
	}
	cases := []tc{
		{
			name: "in-txn swap accepted",
			seed: []Mutation{
				{key: "int:1", row: Row{key: "int:1", uniq: intKey(100)}},
				{key: "int:2", row: Row{key: "int:2", uniq: intKey(200)}},
			},
			commit: []Mutation{
				{key: "int:1", row: Row{key: "int:1", uniq: intKey(200)}},
				{key: "int:2", row: Row{key: "int:2", uniq: intKey(100)}},
			},
			wantError: false,
		},
		{
			name: "reuse released value accepted",
			seed: []Mutation{
				{key: "int:1", row: Row{key: "int:1", uniq: intKey(100)}},
			},
			commit: []Mutation{
				{key: "int:1", row: Row{key: "int:1", uniq: intKey(999)}},
				{key: "int:2", row: Row{key: "int:2", uniq: intKey(100)}}, // 复用被释放的 100
			},
			wantError: false,
		},
		{
			name: "reuse after delete accepted",
			seed: []Mutation{
				{key: "int:1", row: Row{key: "int:1", uniq: intKey(100)}},
			},
			commit: []Mutation{
				{key: "int:1", delete: true},
				{key: "int:2", row: Row{key: "int:2", uniq: intKey(100)}},
			},
			wantError: false,
		},
		{
			name: "true conflict rejected",
			seed: []Mutation{
				{key: "int:1", row: Row{key: "int:1", uniq: intKey(100)}},
				{key: "int:2", row: Row{key: "int:2", uniq: intKey(200)}},
			},
			commit: []Mutation{
				{key: "int:2", row: Row{key: "int:2", uniq: intKey(100)}}, // 抢 int:1 的值
			},
			wantError: true,
		},
		{
			name: "two keys same new value rejected",
			seed: []Mutation{
				{key: "int:1", row: Row{key: "int:1", uniq: intKey(1)}},
				{key: "int:2", row: Row{key: "int:2", uniq: intKey(2)}},
			},
			commit: []Mutation{
				{key: "int:1", row: Row{key: "int:1", uniq: intKey(300)}},
				{key: "int:2", row: Row{key: "int:2", uniq: intKey(300)}},
			},
			wantError: true,
		},
		{
			name: "multiple nulls accepted",
			seed: []Mutation{
				{key: "int:1", row: Row{key: "int:1", uniq: ""}},
			},
			commit: []Mutation{
				{key: "int:2", row: Row{key: "int:2", uniq: ""}},
				{key: "int:3", row: Row{key: "int:3", uniq: ""}},
			},
			wantError: false,
		},
	}
	build := func() (*DirectionA, *DirectionB, *DirectionC) {
		a, b, c := newA(), newB(), newC()
		return a, b, c
	}
	fail := 0
	for _, tc := range cases {
		a, b, c := build()
		// 三方向各自施加相同 seed
		a.store.apply(tc.seed)
		b.store.apply(tc.seed)
		b.rebuild()
		c.store.apply(tc.seed)
		for _, m := range tc.seed {
			c.tree.add(m.row.uniq, m.key)
		}
		ea := a.check(tc.commit)
		eb := b.check(tc.commit)
		ec := c.check(tc.commit)
		got := func(e error) bool { return e != nil }
		ok := got(ea) == tc.wantError && got(eb) == tc.wantError && got(ec) == tc.wantError
		if !ok {
			fail++
		}
		fmt.Printf("[correctness] %-30s want=%-5v  A=%-5v B=%-5v C=%-5v  %s\n",
			tc.name, tc.wantError, got(ea), got(eb), got(ec), map[bool]string{true: "OK", false: "MISMATCH"}[ok])
	}
	if fail > 0 {
		fmt.Fprintf(os.Stderr, "FATAL %d correctness mismatches\n", fail)
		os.Exit(2)
	}
	fmt.Println()
}

func run(wl workload) {
	commits := wl.gen()

	// A
	a := newA()
	seedStore(a.store, wl)
	t0 := time.Now()
	rcA := 0
	for _, w := range commits {
		if err := a.commit(w); err != nil {
			rcA++
		}
	}
	elA := time.Since(t0)
	base := memOf(a)

	// B
	b := newB()
	seedStore(b.store, wl)
	b.rebuild() // 建立常驻 owner（等同于建索引/恢复后的重建）
	t0 = time.Now()
	rcB := 0
	for _, w := range commits {
		if err := b.commit(w); err != nil {
			rcB++
		}
	}
	elB := time.Since(t0)
	memB := memOf(b)

	// 恢复责任计时：B 从最终 store 全量重建 owner
	t0 = time.Now()
	rbEntries := b.rebuild()
	rbElapsed := time.Since(t0)

	// C
	c := newC()
	seedStore(c.store, wl)
	// 重建历史树（恢复时 index.Build 也是全量）
	for key, chain := range c.store.chains {
		for _, v := range chain {
			if !v.deleted {
				c.tree.add(v.row.uniq, key)
			}
		}
	}
	t0 = time.Now()
	rcC := 0
	for _, w := range commits {
		if err := c.commit(w); err != nil {
			rcC++
		}
	}
	elC := time.Since(t0)
	memC := memOf(c)

	// 一致性：稳态合法负载下三方向都必须接受全部提交（冲突数都为 0）
	if rcA != 0 || rcB != 0 || rcC != 0 {
		fmt.Fprintf(os.Stderr, "FATAL unexpected conflicts A=%d B=%d C=%d on %s (steady workload must be legal)\n", rcA, rcB, rcC, wl.name)
		os.Exit(2)
	}

	fmt.Printf("=== workload=%s N=%d domain=%d commits=%d batch=%d kind=%s swap=%v ===\n",
		wl.name, wl.keys, wl.domain, wl.commits, wl.batch, map[bool]string{true: "text", false: "int"}[wl.text], wl.swap)
	fmt.Printf("%-3s %12s %10s %14s %14s %14s %12s %12s\n",
		"dir", "elapsed", "conflicts", "rows_scanned", "lookups", "cand_rows", "hist_entries", "heap_B")
	fmt.Printf("%-3s %12s %10d %14d %14s %14s %12s %12d\n",
		"A", elA.Round(time.Microsecond), rcA, a.rowsScanned, "-", "-", "-", base)
	fmt.Printf("%-3s %12s %10d %14s %14d %14s %12s %12d  rebuild=%s entries=%d\n",
		"B", elB.Round(time.Microsecond), rcB, "-", b.touchedLookups, "-", "-", memB, rbElapsed.Round(time.Microsecond), rbEntries)
	fmt.Printf("%-3s %12s %10d %14s %14s %14d %12d %12d\n",
		"C", elC.Round(time.Microsecond), rcC, "-", "-", c.candidateRows, c.tree.size(), memC)
	fmt.Printf("resident-extra B-over-A ~ %d B ; C-over-A ~ %d B\n",
		diff(memB, base), diff(memC, base))
	fmt.Println()
}

func diff(x, y uint64) int64 { return int64(x) - int64(y) }

func main() {
	scale := flag.String("scale", "standard", "standard | large | correctness")
	flag.Parse()

	if *scale == "correctness" {
		correctness()
		return
	}

	workloads := []workload{
		// 调用方画像：很多小更新（batch=1..4），少量大批调整（batch=200/500）
		{name: "small-int", keys: 10000, domain: 60000, commits: 2000, batch: 2, seed: 42},
		{name: "small-swap", keys: 10000, domain: 10000, commits: 2000, batch: 2, seed: 43, swap: true},
		{name: "small-text", keys: 10000, domain: 60000, commits: 2000, batch: 2, seed: 44, text: true},
		{name: "bigbatch", keys: 10000, domain: 60000, commits: 40, batch: 250, seed: 45},
		{name: "bigbatch-swap", keys: 10000, domain: 10000, commits: 40, batch: 250, seed: 46, swap: true},
		{name: "grow-reuse", keys: 10000, domain: 200000, commits: 2000, batch: 2, seed: 47},
	}
	if *scale == "large" {
		workloads = []workload{
			{name: "large-small", keys: 100000, domain: 400000, commits: 4000, batch: 2, seed: 52},
			{name: "large-swap", keys: 100000, domain: 100000, commits: 4000, batch: 2, seed: 53, swap: true},
			{name: "large-bigbatch", keys: 100000, domain: 400000, commits: 80, batch: 500, seed: 54},
			{name: "large-reuse", keys: 100000, domain: 900000, commits: 4000, batch: 2, seed: 55},
		}
	}
	for _, wl := range workloads {
		run(wl)
	}
}
