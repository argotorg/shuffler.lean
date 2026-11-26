"""Read Lean source imports without reading comments or string contents."""

import re

def without_comments(source: str) -> str:
    out = []
    depth, i, quoted = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif quoted:
            if source[i] == "\\":
                out.extend("  ")
                i += 2
            elif source[i] == '"':
                quoted = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


def imports(source: str) -> tuple[str, ...]:
    pattern = r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\n]+)"
    return tuple(word for match in re.finditer(pattern, without_comments(source), re.M)
                 for word in match.group(1).split())

