#!/usr/bin/env python3
"""Compare all distributed files with the recorded SHA-256 manifest."""
from hashlib import sha256
from pathlib import Path

root = Path(__file__).resolve().parent
manifest = root / 'SHA256SUMS'
entries = manifest.read_text().splitlines()
if not entries:
    raise SystemExit('Empty SHA256SUMS')
seen = set()
for entry in entries:
    digest, separator, name = entry.partition('  ')
    if not separator or len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
        raise SystemExit(f'Malformed checksum entry: {entry!r}')
    path = (root / name).resolve()
    if not path.is_relative_to(root) or name in seen:
        raise SystemExit(f'Invalid or duplicate path: {name!r}')
    seen.add(name)
    if not path.is_file():
        raise SystemExit(f'Missing file: {name}')
    actual = sha256(path.read_bytes()).hexdigest()
    if actual != digest:
        raise SystemExit(f'Checksum mismatch: {name}')
print(f'All {len(seen)} recorded files match SHA256SUMS.')
