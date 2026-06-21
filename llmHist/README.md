# llmHist — LLM Artifacts for Bit-Vector Invertibility Condition Verification

This directory archives the artifacts produced by working with **Claude Code** (Anthropic's AI coding assistant) to formally verify cvc5's bit-vector invertibility conditions in Coq 8.20.0. It is included alongside the proof source to document the LLM-assisted development process for reproducibility and research purposes.

**Total proof time:** 40 hours, 7 minutes, 14 seconds  
**Average per proof:** 2 hours, 13 minutes, 44 seconds

---

## Project Background

The proofs in this repository establish correctness of bit-vector *invertibility conditions* — predicates of the form `(∃x. f(x) op t) ↔ g(s, t)` over fixed-width bit-vectors — as used by the cvc5 SMT solver (Niemetz et al.). The core files are:

- `BVList.v` — the bit-vector library (~14k lines); helper lemmas live here.
- `InvCond.v` — the invertibility condition proofs.
- `DepInvCond.v` — lifts `InvCond.v` proofs to Coq's dependent `bitvector n` type.

All proof work was done interactively with Claude Code across 18 main proofs plus a final lift of 38 theorems into dependent types (28 + 38 = 66 theorems total, zero `Admitted`).

---

## What is Claude Code?

[Claude Code](https://claude.ai/code) is Anthropic's CLI tool that runs Claude (a large language model) as an interactive coding assistant. It operates in a terminal, reads and edits files directly, runs shell commands, and maintains project state across sessions through:

- **`CLAUDE.md`** — a project instruction file it reads at the start of every session.
- **`.claude/`** — a directory holding project-level settings, permissions, and configuration.
- **`~/.claude/`** — the user's home-level directory where Claude Code stores conversation logs, memory, plans, and global settings. The contents of `~/.claude/` are what populate this `llmHist/` directory.
- **Memory files** — structured notes Claude Code writes to itself to remember patterns and progress across sessions.
- **Plans** — structured implementation plans Claude Code produces before making changes.

Conversation logs are stored automatically by Claude Code in `~/.claude/projects/<project-path>/` on the development machine. They are not committed to the repository by default; the contents of this directory were manually copied here to document the process.

---

## Files and Directories

| Path | Description |
|------|-------------|
| `CLAUDE.md` | Project instruction file auto-loaded by Claude Code at the start of every session. Documents the proof workflow, build commands, lemma lookup strategy, and known Coq 8.20.0 quirks accumulated over the course of the project. |
| `HANDOFF.md` | A handoff document written mid-project to capture the exact state of `bvmult_sgt` so work could be resumed in a new session. Includes the failing proof skeleton, two helper lemmas in progress, and the one-line fix needed to unblock compilation. |
| `test_scratch.v` | A temporary Coq file an agent created during proof development to isolate and debug errors in isolation before writing the final fix into `InvCond.v` and `BVList.v`. |
| `.claudeignore` | Tells Claude Code which files to skip when reading the project (analogous to `.gitignore`). Prevents Claude Code from reading large compiled artifacts (`.vo`, `.glob`, etc.). |
| `.claude/` | Project-level Claude Code settings. `settings.json` configures model and permissions; `settings.local.json` holds machine-local overrides (e.g., auto-approved shell commands). |
| `memory/` | Persistent memory files written by Claude Code to retain information across sessions. `MEMORY.md` is an index; `project_status.md` tracks proof completion; `proof_patterns.md` records recurring tactics and Coq 8.20.0 gotchas discovered during proofs. |
| `plans/` | Structured implementation plans produced by Claude Code before undertaking multi-step tasks. See [Plans](#plans) below. |
| `logs/` | Full conversation histories, one `.jsonl` file per session. Each `.jsonl` is a sequence of JSON objects recording the full exchange between the user and Claude Code. Sessions that spawned sub-agents include a same-name subdirectory with those sub-conversations. See [Proof Session Logs](#proof-session-logs) below. |

---

## Plans

Plans are documents Claude Code writes before implementing non-trivial changes, capturing its reasoning and proposed approach for user review.

| File | Description |
|------|-------------|
| `plans/dep-invcond-38-missing-theorems.md` | Plan for lifting 38 theorems from `InvCond.v` into `DepInvCond.v` using Coq's dependent `bitvector n` sigma type. Includes the standard proof template, per-theorem notes on argument order and `bv_eq_reflect` usage, and a full list of all 38 theorems. |

---

## Proof Session Logs

All conversation logs are in `logs/`. Documented proof sessions are numbered `01`–`08`; auxiliary and undocumented sessions retain their original UUID filenames.

The first six sessions (01–04) occurred when the repository was named `vibe-proving`; sessions 05–08 occurred after it was renamed to `bitvector-vibe-proving`. Both sets of logs are collected here without distinction.

### Documented Sessions

| Session | Proof(s) | Log file | Sub-agents? |
|---------|----------|----------|-------------|
| 1 | bvshl_sle, bvshl_sle2, bvshl_slt2 | `01-bvshl-sle-sle2-slt2.jsonl` | Yes |
| 2 | bvashr_sle2 | `02-bvashr-sle2.jsonl` | No |
| 3 | bvashr_sgt2 | `03-bvashr-sgt2.jsonl` | No |
| 4 | bvand_sge | `04-bvand-sge.jsonl` | No |
| 5 | bvor_slt | `05-bvor-slt.jsonl` | No |
| 6 | bvmult_slt | `06-bvmult-slt.jsonl` | No |
| 7 | bvmult_sgt (partial), bvmult_sle, bvmult_sge | `07-bvmult-sgt-sle-sge-pt1.jsonl` | Yes |
| 8 | bvmult_sge (cont.), bvudiv_uge, bvudiv_reverse_neq, bvudiv_reverse_sgt, bvudiv_reverse_sge, bvurem_slt, bvurem_sle, bvurem_reverse_eq, bvurem_reverse_sgt, bvurem_reverse_sge; **DepInvCond.v: 38 theorems lifted to dependent bitvector types** (66 total, zero Admitted) | `08-bvmult-sge-bvudiv-bvurem-dep-invcond.jsonl` | Yes |

### Auxiliary Sessions

The remaining UUID-named `.jsonl` files are setup, exploration, or maintenance sessions not directly tied to a single proof. They include early project scaffolding, experimentation with proof strategies, and the session in which `llmHist/` itself was created.

### Sub-agent Logs

Some sessions spawned one or more sub-agents — parallel Claude Code instances delegated a specific sub-task (e.g., searching the codebase for a lemma while the main agent continued proof work). When a session has sub-agents, its logs are organized as:

```
logs/
├── 07-bvmult-sgt-sle-sge-pt1.jsonl     ← main conversation
└── 07-bvmult-sgt-sle-sge-pt1/
    └── subagents/
        ├── agent-<id>.jsonl             ← sub-agent conversation
        └── agent-<id>.meta.json         ← sub-agent metadata (type, prompt)
```

`tool-results/` subdirectories (present in sessions 01 and 08) contain cached outputs of tool calls that were too large to embed inline in the `.jsonl`.

---

## File Provenance

These files originate from the development machine's `~/.claude/` directory, which Claude Code manages automatically:

| Source path | Contents | Destination here |
|-------------|----------|-----------------|
| `~/.claude/projects/<project>/` | Conversation logs (`.jsonl`) | `logs/` |
| `~/.claude/projects/<project>/memory/` | Persistent memory files | `memory/` |
| `~/.claude/plans/` | Planning documents | `plans/` |
| `<repo-root>/CLAUDE.md` | Project instructions | `CLAUDE.md` |
| `<repo-root>/.claudeignore` | Claude Code ignore rules | `.claudeignore` |
| `<repo-root>/.claude/` | Project settings | `.claude/` |

---

## Reproducing Similar Work

To set up a comparable Claude Code workflow in another Coq project, restore the following files to the indicated locations:

| File/dir | Restore to | Purpose |
|----------|-----------|---------|
| `CLAUDE.md` | `<repo-root>/CLAUDE.md` | Auto-loaded as project instructions each session |
| `.claudeignore` | `<repo-root>/.claudeignore` | Prevents Claude Code from reading compiled artifacts |
| `.claude/` | `<repo-root>/.claude/` | Project-level settings and permissions |
| `memory/` | `~/.claude/projects/<repo-path>/memory/` | Restores persistent memory across sessions |

Claude Code will auto-load `CLAUDE.md` and `.claude/` at session start. The memory files will be picked up from `~/.claude/` automatically. The proof workflow, lemma search strategy, and Coq 8.20.0 workarounds documented in `CLAUDE.md` and `memory/proof_patterns.md` are the main artifacts to adapt for a new project.
