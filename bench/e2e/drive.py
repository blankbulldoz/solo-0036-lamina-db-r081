#!/usr/bin/env python3
"""
端到端负载：驱动真实 laminad 二进制（基线 = 方向 A，每次提交全表 Scan 重建唯一 set）。
不修改内核。测量：
  1) 小更新 / 大批调整两类提交的端到端延迟（HTTP 往返，含 fsync 提交）
  2) 同事务唯一值置换、跨提交值复用、真冲突的真实 HTTP 判定
  3) 重启恢复耗时（Open 时对每个关系跑一遍全表唯一校验）
所有实例使用独立临时目录，结束清理。
"""
import argparse, json, os, random, shutil, signal, subprocess, sys, tempfile, time, urllib.request, urllib.error

class Client:
    def __init__(self, base):
        self.base = base
    def _call(self, method, path, body=None, timeout=30):
        data = None if body is None else json.dumps(body).encode()
        req = urllib.request.Request(self.base + path, data=data, method=method,
                                     headers={"Content-Type": "application/json"})
        t0 = time.perf_counter()
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.status, json.loads(r.read()), time.perf_counter() - t0
        except urllib.error.HTTPError as e:
            return e.code, json.loads(e.read()), time.perf_counter() - t0

    def wait_ready(self, deadline=30):
        end = time.time() + deadline
        while time.time() < end:
            try:
                st, _, _ = self._call("GET", "/v1/lamina/health")
                if st == 200:
                    return
            except Exception:
                pass
            time.sleep(0.05)
        raise RuntimeError("server not ready")

def start(binary, data, addr):
    log = open(os.path.join(data, "server.log"), "wb")
    p = subprocess.Popen([binary, "-data", data, "-listen", addr],
                         stdout=log, stderr=subprocess.STDOUT)
    c = Client("http://" + addr)
    c.wait_ready()
    return p, c

def stop(p):
    p.send_signal(signal.SIGTERM)
    p.wait(timeout=15)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", default="/tmp/laminad-baseline")
    ap.add_argument("--sizes", default="1000,5000,20000")
    ap.add_argument("--small-commits", type=int, default=400)
    ap.add_argument("--seed", type=int, default=7)
    args = ap.parse_args()

    random.seed(args.seed)
    root = tempfile.mkdtemp(prefix="lamina-e2e-")
    import socket
    s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
    addr = f"127.0.0.1:{port}"
    data = os.path.join(root, "data")
    os.makedirs(data, exist_ok=True)
    p = None
    try:
        t_start = time.perf_counter()
        p, c = start(args.binary, data, addr)
        boot1 = time.perf_counter() - t_start

        # 建关系 + 唯一索引（先建索引，写入即受约束；CreateIndex 本身也跑一次全表校验）
        st, _, _ = c._call("POST", "/v1/lamina/relations", {
            "name": "spectra", "primary": "sample",
            "columns": [{"name": "sample", "type": "int"},
                        {"name": "band", "type": "text"},
                        {"name": "amplitude", "type": "int", "nullable": True}]})
        assert st == 201, st
        st, _, _ = c._call("POST", "/v1/lamina/indexes",
                           {"name": "uniq_band", "relation": "spectra", "column": "band", "unique": True})
        assert st == 201, st

        def begin():
            st, out, _ = c._call("POST", "/v1/lamina/transactions", {})
            assert st == 201, out
            return out["id"]
        def put(tx, sample, band, insert_only=False):
            st, out, _ = c._call("POST", f"/v1/lamina/transactions/{tx}/put",
                                 {"relation": "spectra",
                                  "row": {"sample": sample, "band": band, "amplitude": None},
                                  "insert_only": insert_only})
            return st
        def commit(tx):
            return c._call("POST", f"/v1/lamina/transactions/{tx}/commit")
        def delete(tx, sample):
            return c._call("POST", f"/v1/lamina/transactions/{tx}/delete",
                           {"relation": "spectra", "key": sample})

        # ---- 语义正确性（真实 HTTP）----
        print("== semantic cases on real engine ==")
        tx = begin()
        assert put(tx, 1, "b100", True) == 200
        assert put(tx, 2, "b200", True) == 200
        st, _, _ = commit(tx); assert st == 200, ("seed commit", st)

        # 同事务置换 b100<->b200，必须接受
        tx = begin()
        assert put(tx, 1, "b200") == 200
        assert put(tx, 2, "b100") == 200
        st, out, _ = commit(tx)
        print(f"  in-txn swap: HTTP {st} (expect 200) {out if st!=200 else ''}")
        assert st == 200, out

        # 跨提交：释放 b100 后另一键复用，必须接受
        tx = begin()
        assert put(tx, 2, "b999") == 200   # 2 让出 b100
        assert put(tx, 3, "b100", True) == 200  # 新键 3 复用 b100
        st, out, _ = commit(tx)
        print(f"  reuse released value: HTTP {st} (expect 200) {out if st!=200 else ''}")
        assert st == 200, out

        # 删除后复用，必须接受
        tx = begin()
        st, _, _ = delete(tx, 1)
        assert st == 200
        assert put(tx, 4, "b200", True) == 200  # 1 已删，b200 现归 4
        st, out, _ = commit(tx)
        print(f"  reuse after delete: HTTP {st} (expect 200) {out if st!=200 else ''}")
        assert st == 200, out

        # 真冲突：两个键抢同一仍被占用的值，必须 409
        tx = begin()
        assert put(tx, 5, "b999", True) == 200  # b999 仍被键 2 持有
        st, out, _ = commit(tx)
        print(f"  true conflict: HTTP {st} (expect 409) code={out.get('error',{}).get('code')}")
        assert st == 409, out

        # 多个 null，必须接受
        tx = begin()
        for s in (6, 7, 8):
            st2, _, _ = c._call("POST", f"/v1/lamina/transactions/{tx}/put",
                                {"relation": "spectra",
                                 "row": {"sample": s, "band": f"bn{s}", "amplitude": None}})
            assert st2 == 200
        st, out, _ = commit(tx)
        print(f"  multiple nulls (amplitude): HTTP {st} (expect 200)")
        assert st == 200, out
        print()

        # ---- 规模扫描：不同 N 下的小提交与大批提交延迟 ----
        print("== commit latency vs relation size (baseline full-scan) ==")
        print(f"{'N':>7} {'small_p50_ms':>13} {'small_p95_ms':>13} {'bigbatch_ms':>13} {'reopen_ms':>11}")

        def fill_to(target):
            # 单事务写集上限 1000，按 900 分块填充；band 唯一。
            existing = set()
            st, stats, _ = c._call("GET", "/v1/lamina/stats")
            have = stats["keys"]
            if have >= target:
                return
            todo = target - have
            # 从 max+1 开始分配新主键
            start_id = target  # 简单起见直接用 target 之上的号段避免与早期语义行冲突
            n = 0
            while n < todo:
                tx = begin()
                for _ in range(min(900, todo - n)):
                    sid = start_id + n
                    stp = put(tx, sid, f"fill-{sid:08d}", True)
                    assert stp == 200, ("fill put", stp)
                    n += 1
                st, out, _ = commit(tx)
                assert st == 200, ("fill commit", out)
            st, stats, _ = c._call("GET", "/v1/lamina/stats")
            assert stats["keys"] >= target, (stats["keys"], target)

        for size in [int(x) for x in args.sizes.split(",")]:
            fill_to(size)

            # 小更新提交（每事务 2 行），band 在未占用空间取新值
            lat = []
            for i in range(args.small_commits):
                tx = begin()
                s1 = random.randint(1, size)
                s2 = random.randint(1, size)
                put(tx, s1, f"u-{size}-{i}-a")
                if s2 != s1:
                    put(tx, s2, f"u-{size}-{i}-b")
                st, out, dt = commit(tx)
                assert st == 200, out
                lat.append(dt * 1000)
            lat.sort()
            p50 = lat[len(lat) // 2]
            p95 = lat[int(len(lat) * 0.95)]

            # 大批调整：一个事务 500 行，用未占用新值（写集上限内）
            tx = begin()
            victims = random.sample(range(1, size + 1), min(500, size))
            for j, s in enumerate(victims):
                put(tx, s, f"batch-{size}-{j:05d}")
            st, out, big_dt = commit(tx)
            assert st == 200, out

            # 重启恢复：计时进程重启（Open 含每关系全表唯一校验 + index.Build 重建）
            stop(p)
            t0 = time.perf_counter()
            p, c = start(args.binary, data, addr)
            reopen = (time.perf_counter() - t0) * 1000

            print(f"{size:>7} {p50:>13.3f} {p95:>13.3f} {big_dt*1000:>13.3f} {reopen:>11.2f}")

        # 最终 stats
        st, stats, _ = c._call("GET", "/v1/lamina/stats")
        print("\nfinal stats:", json.dumps({k: stats[k] for k in
              ("sequence", "keys", "versions", "index_entries", "commits_since_open", "conflicts_since_open")},
              ensure_ascii=False))
        stop(p)
    finally:
        if p is not None and p.poll() is None:
            p.kill()
        shutil.rmtree(root, ignore_errors=True)

if __name__ == "__main__":
    main()
