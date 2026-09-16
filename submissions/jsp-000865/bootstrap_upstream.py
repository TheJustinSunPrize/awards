"""Fetch the unchanged attributed prerequisite and verify the immutable bytes."""
from pathlib import Path
import hashlib, json, urllib.request

def bootstrap():
    root = Path(__file__).resolve().parent
    pin = json.loads((root/'upstream-pin.json').read_text(encoding='utf-8'))
    target = root/'JSP000865/Upstream.lean'
    if target.is_file():
        data = target.read_bytes()
    else:
        request = urllib.request.Request(pin['raw_url'], headers={'User-Agent': 'JSP000865-reproducer'})
        with urllib.request.urlopen(request, timeout=120) as response:
            data = response.read()
    if len(data) != pin['bytes'] or hashlib.sha256(data).hexdigest() != pin['sha256']:
        raise SystemExit('Pinned prerequisite does not match; refusing to overwrite or compile')
    target.parent.mkdir(exist_ok=True)
    target.write_bytes(data)
    return pin

if __name__ == '__main__':
    print(json.dumps(bootstrap(), indent=2))
