"""从 Lean 官方发行页分段下载固定版本，并核对官方 SHA-256。"""

from concurrent.futures import ThreadPoolExecutor, as_completed
from hashlib import sha256
from pathlib import Path
from urllib.request import ProxyHandler, Request, build_opener
import time

ROOT = Path(__file__).resolve().parents[1]
DOWNLOADS = ROOT / ".work" / "lean-tools"
PARTS = DOWNLOADS / "parts-4.34.0"
ARCHIVE = DOWNLOADS / "lean-4.34.0-windows.tar.zst"
ASSET = "https://api.github.com/repos/leanprover/lean4/releases/assets/563514497"
SIZE = 588837341
DIGEST = "c07e88d1fe4839ec96a79f54637b2a3a983ea6c5b7e82ff35afa22a7700a86b7"
CHUNK = 4 * 1024 * 1024


def opener():
    # 当前机器的全局代理不可用，本次下载使用直连。
    return build_opener(ProxyHandler({}))


def file_digest(path):
    digest = sha256()
    with path.open("rb") as stream:
        while block := stream.read(8 * 1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def main():
    DOWNLOADS.mkdir(parents=True, exist_ok=True)
    PARTS.mkdir(exist_ok=True)
    if ARCHIVE.exists() and ARCHIVE.stat().st_size == SIZE:
        if file_digest(ARCHIVE) == DIGEST:
            print("官方工具链压缩包已完整下载并通过校验。", flush=True)
            return

    # 临时签名地址只留在内存中，不写入日志或项目文件。
    request = Request(ASSET, headers={
        "User-Agent": "JSP628-Research",
        "Accept": "application/octet-stream",
        "Range": "bytes=0-0",
    })
    with opener().open(request, timeout=30) as response:
        address = response.geturl()
        if response.status != 206:
            raise RuntimeError("官方服务器没有按请求返回分段下载响应")

    count = (SIZE + CHUNK - 1) // CHUNK

    def fetch(index):
        start = index * CHUNK
        end = min(SIZE, start + CHUNK) - 1
        expected = end - start + 1
        path = PARTS / f"{index:04d}.part"
        if path.exists() and path.stat().st_size == expected:
            return expected
        for attempt in range(3):
            try:
                req = Request(address, headers={
                    "User-Agent": "JSP628-Research",
                    "Range": f"bytes={start}-{end}",
                })
                with opener().open(req, timeout=45) as source:
                    if source.status != 206 or source.headers.get("Content-Range") != f"bytes {start}-{end}/{SIZE}":
                        raise RuntimeError("分段响应范围与请求不一致")
                    with path.open("wb") as target:
                        while data := source.read(128 * 1024):
                            target.write(data)
                if path.stat().st_size != expected:
                    raise RuntimeError("分段文件长度不符")
                return expected
            except Exception as error:
                if attempt == 2:
                    # 不输出含临时签名地址的异常内容。
                    raise RuntimeError(f"分段 {index} 下载失败：{type(error).__name__}") from None
                print(f"分段 {index} 第 {attempt + 1} 次下载失败，重试。", flush=True)
                time.sleep(1)

    done = 0
    with ThreadPoolExecutor(max_workers=16) as pool:
        for future in as_completed([pool.submit(fetch, i) for i in range(count)]):
            done += future.result()
            print(f"已完成 {done / 1024 / 1024:.1f} / {SIZE / 1024 / 1024:.1f} MiB", flush=True)

    with ARCHIVE.open("wb") as target:
        for index in range(count):
            with (PARTS / f"{index:04d}.part").open("rb") as source:
                while data := source.read(1024 * 1024):
                    target.write(data)
    actual = file_digest(ARCHIVE)
    if actual != DIGEST:
        raise RuntimeError("完整工具链压缩包的 SHA-256 与官方记录不符")
    print(f"下载完成，SHA-256：{actual}", flush=True)


if __name__ == "__main__":
    main()
