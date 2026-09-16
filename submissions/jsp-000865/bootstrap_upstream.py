"""Fetch the unchanged pinned third-party prerequisite; verify bytes before use."""
from pathlib import Path
import hashlib,json,urllib.request
root=Path(__file__).resolve().parent
pin=json.loads((root/'upstream-pin.json').read_text(encoding='utf-8'))
data=urllib.request.urlopen(pin['raw_url'],timeout=120).read()
if hashlib.sha256(data).hexdigest()!=pin['sha256']:
    raise SystemExit('Pinned upstream SHA256 mismatch')
(root/'JSP000865/Upstream.lean').write_bytes(data)
print('Pinned upstream source verified')
