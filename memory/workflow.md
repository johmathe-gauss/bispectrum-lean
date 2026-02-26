# Workflow & Context Management

## Philosophy
Treat Gauss as a collaborator with:
- **Perfect recall** of written notes
- **Imperfect recall** of pure conversation
- **Fast context rebuild** from structured files

## Directory Structure

```
/workspace/group/
├── memory/           # Long-term knowledge
│   ├── project_overview.md
│   ├── math_foundations.md
│   ├── implementation_notes.md
│   ├── decisions.md
│   └── workflow.md (this file)
├── sessions/         # Session logs
│   └── YYYY-MM-DD_description.md
├── active/           # Current work state
│   ├── current_task.md
│   └── blockers.md
└── code/            # Working code (when not in main repo)
```

## Session Protocol

### Starting a Session
**Johan provides context pointer:**
- Brief: "Continue SO(3) implementation"
- Or: "Read sessions/2026-02-22.md"

**Gauss rebuilds context:**
1. Read current_task.md
2. Check blockers.md
3. Scan relevant memory files (~2 min)
4. Confirm understanding & proceed

### During Work
- Document insights in memory/ as discovered
- Track decisions in decisions.md
- Keep code self-documenting with math references
- Write tests that demonstrate concepts

### Ending a Session
1. Write session summary to sessions/
2. Update current_task.md for next time
3. Update blockers.md with open questions
4. Commit any code changes

## Communication Styles

### For Deep Work (Johan can be terse)
- "Fix CG coefficient bug" → I check notes for context
- "Implement D_n inversion" → I know the paper
- "Run overnight tests" → I document as I go

### For New Directions (Johan provides detail)
- The goal
- Why we're doing it
- Constraints/preferences

## Context Compression

**If session gets long:**
1. Summarize intermediate work to file
2. Clear working notes
3. Continue with summary

**For overnight work:**
- Get clear goal
- Write `active/checkpoint.md` every ~30 min (resumption point, not a log)
- Send Telegram progress updates at major milestones via `mcp__nanoclaw__send_message`
- Write detailed handoff in `current_task.md` at end
- Checkpoint format: "what I just did, where I am, exact next step, gotchas"

## Communication

- **Progress updates**: Send via Telegram (mcp__nanoclaw__send_message) during long runs
- **Major milestones**: Always notify (e.g., "cyclic bispectrum implemented + tests passing")
- **Blockers**: Notify immediately if stuck on something that needs Johan's input
- **Completion**: Final summary message when overnight task is done

## active/checkpoint.md Format

```
# Checkpoint [TIME]

## Just completed
[1-2 sentences]

## Current state
[Exact file/function I'm in, what's done, what's partial]

## Next step
[Specific, actionable — enough to resume cold]

## Gotchas
[Anything non-obvious I discovered]
```

## File Naming Conventions

- **Dates**: YYYY-MM-DD format
- **Code**: snake_case
- **Docs**: descriptive_name.md
- **Tests**: test_feature.py

## What Goes Where

**memory/project_overview.md**
- High-level goals
- Architecture decisions
- Current status
- Next steps

**memory/math_foundations.md**
- Key theorems
- Derivations
- Formulas
- Paper references

**memory/implementation_notes.md**
- Code structure
- Design patterns
- API decisions
- Performance notes

**memory/decisions.md**
- "Why X not Y" rationales
- Trade-offs considered
- Rejected approaches

**sessions/DATE_description.md**
- What we did
- What worked
- What didn't
- Insights gained

**active/current_task.md**
- What I'm working on RIGHT NOW
- Concrete next steps
- Partially completed work

**active/blockers.md**
- Open questions
- Waiting on X
- Needs decision from Johan
