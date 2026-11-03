# K1 decider eval: nav-pack context efficiency on jellyfin

Bead: trailtracker-frontier-context-nav-akv · ADR-0004 · 2026-07-07
Updated 2026-07-07 for the dogfood fixes (trailtracker-nav-dogfood-fixes-7nd):
read-plan reserve + hub damping — see "After the dogfood fixes" below.
Reproduce: `JELLYFIN=<checkout> bash scripts/nav_decider_eval.sh`

## Setup

- **Corpus**: jellyfin server checkout — 2,105 files analyzed (2,103 `.cs`),
  11,957,264 source bytes; TrailTracker graph 22,923 nodes / 87,270 edges;
  100% lossless parse; analysis ≈ 0.6 s, full `nav pack` ≈ 0.9 s.
- **Question** (the real task an agent gets): *"where is playback session
  state managed and what breaks if I change it?"*
- **Contenders**:
  - (a) a grep-driven agent that finds candidate files and reads them whole,
  - (b) `trailtracker nav pack "where is playback session state managed"
    <dir> --budget 20000 --json` (chars, not tokens — no tokenizer exists in
    this stack).

## Numbers

| approach | context loaded | ratio vs pack |
|---|---:|---:|
| naive grep (`playback` AND `session`, 97 whole files) | 3,239,245 chars | **169.6×** |
| disciplined grep (top-10 files by match count, whole files) | 228,709 chars | **12.0×** |
| nav pack response (budget 20,000) | 19,097 chars | 1× |
| nav pack + top-10 read-plan spans (the realistic workflow) | 23,480 chars | — |
| nav pack + ALL 55 read-plan spans | 104,597 chars | — |

End-to-end, the realistic pack workflow (pack + the top ten spans it says to
read) costs **23,480 chars against 3,239,245** for the naive whole-file agent
(≈ 138×) and against **228,709** for a disciplined one (≈ 9.7×). The budget
block reported honestly: `used_chars: 19658`, `estimated_chars: 71724` (the
full untruncated pack), `omitted: {edges: 356, read_plan: 9}`.

## Does the pack actually contain the answer? (verified by hand)

Ground truth, established by reading the jellyfin source directly: playback
session state lives in **`Emby.Server.Implementations/Session/
SessionManager.cs`** — `OnPlaybackStart` (line 763) / `OnPlaybackProgress`
(858, 895) / `OnPlaybackStopped` resolve the session and call
`UpdateNowPlayingItem` (389–449), which mutates `session.NowPlayingItem` and
`session.PlayState.{IsPaused, PositionTicks, MediaSourceId}` on
**`MediaBrowser.Controller/Session/SessionInfo.cs`** (`PlayState`, line 54).
The API surface is `Jellyfin.Api/Controllers/PlaystateController.cs`; change
consumers include `SessionInfoWebSocketListener` and the
`PlaybackStartInfo`/`PlaybackProgressInfo` DTOs.

**The 20k pack contains** (all verified present):

- `SessionManager.cs` with exact spans `763–841` (`OnPlaybackStart`) and
  `858–862`/`895–962` (`OnPlaybackProgress`) — the *where*, at method grain;
- `PlaystateController.PingPlaybackSession` (`233–246`), the API entry;
- the three `SessionInfoWebSocketListener.OnSessionManagerPlayback*`
  handlers — who observes the state;
- `PlaybackStartInfo` / `PlaybackProgressInfo` DTO spans;
- the *what-breaks* answer as numbers: per-seed `blast_count` 721–1,818
  (same machinery as `query blast-radius`), plus orientation showing the
  change surface concentrated in `Jellyfin.Api` (Presentation, 140 nodes)
  and `MediaBrowser.Controller` (Application, 30 nodes).

**Verdict: answer contained at file/method grain — with one honest gap.**
`SessionInfo.cs` (the type that physically holds `PlayState`) is named
nowhere in the pack, not even untruncated at budget 200,000. The lexical
tiers can't hit it (its name shares no tokens with "playback") and no
DEPENDS-family edge lands on it within 2 hops of the seeds (the C# frontend
does not emit `USES_TYPE` from the `SessionManager` methods to the
`SessionInfo` parameter type). The pack's top span (`OnPlaybackStart`,
2,627 chars) calls `UpdateNowPlayingItem(session, …)` on its face, so one
follow-up read/`nav_expand` reaches it — but the pack itself stops one hop
short of naming the state holder.

## Other honest findings

1. **Hub noise in the value ranking.** `GuidExtensions.IsNullOrEmpty` ranked
   #1 in the read plan, and ~14 unrelated `Jellyfin.Api` controllers
   (`UpdateUserPassword`, `MergeVersions`, …) rode in as "2 hops from
   PingPlaybackSession": generic utility hubs (`RequestHelpers`,
   `GuidExtensions`) sit 1 hop from everything, and the centrality factor
   rewards exactly the nodes proximity should discount. Fix candidate for a
   follow-up bead: damp nodes reachable from many unrelated seeds
   (IDF-style) or exclude util-archetype hubs from the proximity walk.
   **FIXED 2026-07-07** (trailtracker-nav-dogfood-fixes-7nd) — see below.
2. **Fill order starves the edge list at tight budgets.** At 20k, all 356
   neighborhood edges were omitted (read-plan entries are denser value per
   char and fill first, per ADR-0004). Honest and documented — but an agent
   that wants the wiring must either raise the budget (the full pack is
   71,724 chars) or call `nav_expand` (which is the designed continuation).
3. **Grep converges on the same top-2 files** (`PlaystateController.cs`,
   `SessionManager.cs`) — the pack's advantage is not *finding* the hot
   files but (i) method-grain spans instead of an 81,217-char file, (ii) the
   impact numbers, and (iii) a bounded, deterministic response an agent can
   budget for. The 12× against a disciplined grepper is the number to quote;
   169.6× is the naive ceiling.

## After the dogfood fixes (2026-07-07, trailtracker-nav-dogfood-fixes-7nd)

Same eval, same question, same 20k budget, after ADR-0004's two amendments
(read-plan budget reserve; arrival/waypoint hub tax + IDF multi-seed
damping — formulas in the ADR and `src/nav.rs`).

| metric | before | after |
|---|---:|---:|
| pack response chars (budget 20,000) | 19,097 | 19,051 |
| pack vs naive grep | 169.6× | 170.0× |
| pack vs disciplined grep | **12.0×** | **12.0×** |
| read-plan entries kept | 55 | 52 |
| `GuidExtensions.IsNullOrEmpty` read-plan rank | **#1** | **#30** |
| `GuidExtensions.IsEmpty` rank | #7 | #31 |
| controller files in the read plan | 18 | 4 |
| …of which unrelated to playback/session | 16 | 3 |
| `SessionManager.cs` spans in the plan | 4 | 14 |
| `UpdateNowPlayingItem` (the state mutator) in plan | no | **yes (#15)** |
| `SessionInfo.cs` named anywhere in the pack | **no** | **yes (2 spans)** |

Every previously-contained answer is still contained (`OnPlaybackStart`
span 763 now rank #10; `OnPlaybackProgress` 858 rank #11 and the 963
overload #14 — the 895 overload dropped below the cut but its sibling
entries remain; `PingPlaybackSession` #5; the three WebSocket handlers and
both DTOs present). The top-15 is now essentially all answer material: the
slots the
utility hubs and their riders vacated were taken by `UpdateNowPlayingItem`
(389–449, the method that actually mutates `session.NowPlayingItem` /
`PlayState`) and two `SessionInfo.cs` method spans — which closes the one
honest gap documented above: the pack now names the file that physically
holds the play state (the `PlayState` property itself is still one
follow-up read away; the C# frontend still emits no `USES_TYPE` to it).

The read-plan starvation finding (filed from the live repro
`nav pack "where are domain labels decided" . --budget 6000` on this repo:
zero/one span, seeds+cards ate the budget) is fixed by the reserve: the
same call now returns 9 spans, 0 cards, `used_chars: 5701`, honest
`omitted` counts, `exceeded: false`.

Noise-metric reproduction (after `nav_decider_eval.sh` writes nothing for
this): `trailtracker nav pack "where is playback session state managed"
<jellyfin> --budget 20000 --json | python3 -c 'import json,sys;
p=json.load(sys.stdin); plan=p["read_plan"];
print([i+1 for i,r in enumerate(plan) if "GuidExtensions" in r["path"]],
sorted({r["path"] for r in plan if "/Controllers/" in r["path"]}))'`
