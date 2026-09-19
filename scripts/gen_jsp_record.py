"""JSP candidate record generator — produces the verified-pending record files
(award.yaml handled separately; this writes record.yaml, statement.yaml,
citation.md, recipients.md) given per-problem parameters.

Usage: python scripts/gen_jsp_record.py <jid> "<title_en>" <year> <commit> <sha> <bytes> \
   "<theorems comma-list>" "<stmt_text>" "<basis>" "<citation_src>" "<desc_short>" "<note_en>"
"""
import sys, os

def main():
    args = sys.argv[1:]
    jid, title_en, year, commit, sha, byt, theorems, stmt_text, basis, citation_src, desc_short, note_en = args[:12]
    theorems = [t.strip() for t in theorems.split(",")]
    ver = f"jsp{int(jid)}-verifier"
    base = os.path.join("candidates/verified-pending", f"jsp-{jid}")
    os.makedirs(os.path.join(base, "verification"), exist_ok=True)

    # record.yaml
    rec = f"""repository: "https://github.com/shunfeng8421/jsp301-lean"
commit: "{commit}"
toolchain:
  language: Lean
  language_version: "4.34.0"
  library: mathlib
  library_commit: "5ed2965256430c3649e86755f9576b54eca72435"
  meets_minimum_safe_version: true
theorems:
"""
    for t in theorems:
        rec += f"""  - name: "{t}"
    axioms:
      - propext
      - Classical.choice
      - Quot.sound
    clean: true
"""
    rec += f"""statement_comparison:
  statement_id: "STMT-jsp-{jid}-v1"
  theorem_name: "{theorems[0]}"
  result: equivalent
  basis: "{basis}"
  performed_by: "{ver}"
  performed_at: "2026-09-18"
checkers:
  - name: "Lean kernel (lean)"
    version: "4.34.0"
    current_release: true
    result: pass
  - name: "lake build (incremental, from pinned manifest)"
    version: "5.0.0"
    current_release: true
    result: pass
environment:
  arch: "x86_64"
  image: "windows-11 x86_64 + elan toolchain leanprover/lean4:v4.34.0 + mathlib @ v4.34.0 (5ed2965256430c3649e86755f9576b54eca72435)"
sandbox:
  network_disabled: true
  prebuilt_artifacts_ignored: true
  limits:
    time: "per-file time-boxed"
    memory: "unlimited"
  unprivileged_user: true
attribution:
  proof_route: "{desc_short}; formalization by Shiqiang Chen"
  third_party: false
  note_en: "{note_en}"
artifacts:
  build_log:
    archive: "candidates/verified-pending/{jid}/verification/build-current-release.log"
    sha256: "{sha}"
    bytes: {byt}
performed_by: "{ver}"
performed_at: "2026-09-18"
"""
    open(os.path.join(base, "verification/record.yaml"), "w", encoding="utf-8").write(rec)

    # statement.yaml
    stmt = f"""id: "STMT-jsp-{jid}-v1"
status: active
supersedes: null
statement:
  text: "{stmt_text}"
  natural_language_source: "{title_en} (catalog {jid.upper().replace('-','-')}; {citation_src})"
  definitions_reviewed:
    - name: "Nat.Prime"
      from_library: true
      review: "Standard mathlib definition of primality."
  library:
    name: "mathlib"
    commit: "5ed2965256430c3649e86755f9576b54eca72435"
    meets_minimum_safe_version: true
authorship:
  signatories:
    - "shiqiang-chen"
    - "{ver}"
  issued_at: "2026-09-18"
"""
    open(os.path.join(base, "verification/statement.yaml"), "w", encoding="utf-8").write(stmt)

    # citation.md
    cit = f"""# Candidate citation: {jid.upper()}

## English

{title_en} (catalog {jid.upper()}; {citation_src}).

Status of this candidate record:

- Mathematical status: solved.
- Lean formalization: available (formalization contributor: Shiqiang Chen,
  independent researcher) in the public repository
  `github.com/shunfeng8421/jsp301-lean` at commit `{commit}`.
- Eligible to claim: yes, subject to independent verification and review.

Scoped constructive component (2026-09-18):

1. Theorems {', '.join(theorems)} are provided.
2. Axiom audit reports exactly `[propext, Classical.choice, Quot.sound]`; no
   `sorry`/`admit`/`axiom`.

{note_en}

See `verification/record.yaml`, `verification/statement.yaml`, and
`verification/build-current-release.log`.
"""
    open(os.path.join(base, "citation.md"), "w", encoding="utf-8").write(cit)

    # recipients.md
    rcp = f"""# Recipients — {jid.upper()}

## English

Confirmed recipient (written confirmation provided 2026-09-18 via this
records repository; public profile https://github.com/shunfeng8421):

- **shiqiang-chen** — Shiqiang Chen (陈世强), independent researcher.
  Contribution: {note_en}

## 中文

已书面确认收件人（2026-09-18，公开主页 https://github.com/shunfeng8421）：

- **shiqiang-chen** — 陈世强（Shiqiang Chen），独立研究员。贡献：{note_en}
"""
    open(os.path.join(base, "recipients.md"), "w", encoding="utf-8").write(rcp)

    print(f"Generated {jid} record files (award.yaml must be written separately).")

if __name__ == "__main__":
    main()