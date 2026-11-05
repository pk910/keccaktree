#!/usr/bin/env python3
"""Zero the non-deterministic metadata in a Unix `ar` archive in place.

macOS's BSD `ar`/`ranlib` ignore `SOURCE_DATE_EPOCH` and stamp the real
wall-clock build time (plus uid/gid) into every archive member header, which
makes the resulting `libhashtree.a` differ on every rebuild even when the
compiled object code is byte-for-byte identical. GNU binutils avoids this by
defaulting to deterministic archives; this script reproduces that behaviour for
toolchains that do not, by rewriting the mtime/uid/gid fields of each member
header to 0. The member contents (and therefore the symbol table) are left
untouched, so the archive stays valid and keeps its original (BSD) format.

Usage: zero_ar_metadata.py <archive.a> [<archive.a> ...]
"""
import sys

GLOBAL_HEADER = b"!<arch>\n"
HEADER_SIZE = 60
# Field layout of an `ar` member header (offsets within the 60-byte header).
MTIME = (16, 28)
UID = (28, 34)
GID = (34, 40)
SIZE = (48, 58)


def field(hdr, span):
    return hdr[span[0]:span[1]]


def set_field(buf, span, value):
    width = span[1] - span[0]
    text = str(value).encode("ascii").ljust(width)
    if len(text) > width:
        raise ValueError("value too wide for field")
    buf[span[0]:span[1]] = text


def normalize(path):
    with open(path, "rb") as fh:
        data = bytearray(fh.read())

    if data[:len(GLOBAL_HEADER)] != GLOBAL_HEADER:
        raise SystemExit(f"{path}: not an ar archive")

    off = len(GLOBAL_HEADER)
    members = 0
    while off + HEADER_SIZE <= len(data):
        hdr = data[off:off + HEADER_SIZE]
        if hdr[58:60] != b"`\n":
            raise SystemExit(f"{path}: malformed member header at offset {off}")
        size = int(field(hdr, SIZE).decode("ascii").strip())

        set_field(data, (off + MTIME[0], off + MTIME[1]), 0)
        set_field(data, (off + UID[0], off + UID[1]), 0)
        set_field(data, (off + GID[0], off + GID[1]), 0)

        members += 1
        # Member data follows the header and is padded to an even boundary.
        off += HEADER_SIZE + size + (size & 1)

    with open(path, "wb") as fh:
        fh.write(data)
    print(f"{path}: normalized {members} member header(s)")


def main(argv):
    if len(argv) < 2:
        raise SystemExit(__doc__)
    for path in argv[1:]:
        normalize(path)


if __name__ == "__main__":
    main(sys.argv)
