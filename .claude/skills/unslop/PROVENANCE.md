# Provenance

`SKILL.md` is a verbatim copy of the `unslop` skill from the `pstack` plugin.

- Upstream: https://github.com/michael-denyer/pstack-claude/tree/main/plugins/pstack/skills/unslop
- Original author: Lauren Tan (poteto), who wrote `pstack` for Cursor. The repository above ports
  it to Claude Code.
- Licence: MIT, copied to `LICENSE` in this directory. The MIT terms require that the copyright
  and permission notice travel with the copy, which is why `LICENSE` sits here rather than only in
  the upstream repository.

Vendored rather than installed as a plugin so that it is present in every session without a
network fetch or a marketplace lookup. Sessions in this repository start in a fresh container,
so anything not committed does not exist.

To update, refetch `SKILL.md` and `LICENSE` from the URLs above and commit the diff.
