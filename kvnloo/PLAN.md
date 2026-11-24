# kvnloo/formal-math: prize problems + wallet plan

This fork tracks `anthropics/formal-math` unchanged. Everything of ours lives in `kvnloo/`, so syncing
upstream never conflicts.

## 1. What we already did with upstream (2026-11-23, Mac Studio)

| Project | Result |
|---|---|
| `eth/` | `lake build` OK (9768 jobs, 4 m 12 s, 6.2 GB peak). `ethIsFalse`, `mainTheorem` use only `propext, Classical.choice, Quot.sound`. Own type check `example : MainResults.ETHIsFalse := MainResults.ethIsFalse` compiles. |
| `vp-vnp/` | `lake build` OK (9032 jobs, 8 min, 6.6 GB peak). Five headline theorems, standard axioms only. Own type check of `Statement.Separation` compiles. |
| Buckmaster–Alpöge Navier–Stokes (external repo) | Stopped by the disk watchdog at ~22 % of the proof files, 0 errors. **Not verified.** Needs ~15–17 GB more disk; certificate data not released. |

The Studio copies were deleted afterwards (disk). Do not rebuild Mathlib on the Studio again: a build
is ~13 GB and the internal disk is near its floor. Use the physics-agent prover boxes (section 3).

## 2. Prize problems: which ones, and why

"Prize problems" = open problems that pay money when solved. Ranked by how realistic a payout is for a
Lean-proving agent:

1. **Conjectures.io bounties (primary target).** A marketplace that pays when the Lean checker accepts a
   proof and a human confirms. ~283 problems × 2 modes (prove / counterexample) = 566 tasks. Most
   bounties show ~$2.9k. Recent real payouts (e.g. Erdős 624 and 1068 on 2026-11-19). Submission costs
   one credit (0.25 TAO); checking is free. Pinned to Lean `v4.35.0-rc2`.
   **Key fact found for this plan:** every task id is `fc-v2-<file><theorem>-…`, i.e. the bounties are
   `google-deepmind/formal-conjectures` statements. 171 distinct bounty theorems (342 of 566 task ids)
   map one-to-one onto the formal-conjectures checkout the physics-agent bench already has built
   (`ee50fcb`, all `category research open`). The rest are `parts-*`, `variants-*` and a few named
   conjectures whose slugs need a second mapping pass.
2. **Justin Sun Prize** (1,050 problems, $36–$10k; crypto + KYC; payment not yet confirmed as of 10-14).
   Second priority: same Lean workflow, worse payout evidence.
3. **Erdős's own prizes** ($25–$10k). Overlap with (1); claim through erdosproblems.com when one falls.
4. **Clay Millennium Prizes** ($1M). Not a target for us: payouts need publication + 2 years. We only
   *check* public claims (Navier–Stokes, VP≠VNP-style repos) when they share our Mathlib pin.

Not targets: EFF prime prize (CUDA compute race; Studio is a poor fit), Hutter Prize (compression, not
proof).

## 3. How it plugs into the physics-agent provers

The physics-agent bench (`kvnloo/physics-agent`, branch `bench-hillclimb`) already runs agents against
formal-conjectures and checks every claimed proof with a trusted checker (`prover/leancheck`: statement
fingerprint, axiom list, kernel replay). It runs on:

- **Studio:** shared Lean toolchain + formal-conjectures view with built Mathlib
  (`physics-agent-elan`, `physics-agent-fc-view`). Agents work on a copy under `.lake/pa-work/`.
- **10 Boat boxes:** snapshot `pa-lean-v4-33-1-fc-ee50fcb` (Lean v4.33.1, formal-conjectures ee50fcb
  built), harvested by the "physics-agent boat harvest" cron.

Plug-in, no new Mathlib anywhere:

1. `kvnloo/bounty_map.py` maps the Conjectures.io task list to formal-conjectures theorems
   (output: `kvnloo/bounty_map.json`).
2. The mapped theorems become a bench split (`bench/splits/bounty3.json` for the first run; a
   `bounty` split of all 171 next). Run any arm on it: `bench/run.py --split bounty …`.
3. A theorem that passes leancheck is re-checked against the **Conjectures.io bundle** (Lean
   `v4.35.0-rc2`, their newer Mathlib) with the site's free check before anything is paid. Port
   differences between ee50fcb and their pin are the main risk.
4. Only then: one credit (0.25 TAO) to submit. **That is spending money: Kevin approves each one.**

Results of each run go in `kvnloo/runs/`.

## 4. Wallet libraries

Why a wallet: Conjectures.io charges submissions in TAO (Bittensor) and pays out to a wallet address.

Decision (from the 11-23 research): **no private key ever lives on an agent machine.** Payouts need only
the public `5…` address.

| Option | What it is | Use |
|---|---|---|
| Ledger + Talisman (or TAO.com extension) | Hardware key; each payment approved on the device screen | **Recommended** for buying credits |
| Polkadot Vault | Air-gapped old phone as signer, QR transfer; `btcli --signer vault` | Free alternative to a Ledger |
| Bittensor proxies | Limited-permission second key (e.g. no transfers) | Only if we ever stake |
| Small separate wallet | Only a few TAO for credits | Limits loss if leaked |
| `bittensor-wallet` (Python) | Encrypted key file on disk | **Not used**: key would sit on an agent machine |

Also: the official `conjectures-miner` CLI asks for the wallet password on every paid submit, so it is
not usable unattended; submit through the website with the hardware signer.

Status (2026-11-24): no wallet created, no money spent. Conjectures.io sign-in link sent to Kevin's
inbox; account not yet confirmed. Next owner steps, in order: sign in → (when a proof passes) set up
Talisman + Ledger/Vault and share only the public address → approve each 0.25 TAO submission.

## 5. Status of this plan

- [x] Bounty list → formal-conjectures mapping (171 theorems).
- [x] First prover run on 3 bounty statements: see `kvnloo/runs/2026-11-24-bounty3.md`.
- [ ] Full `bounty` split on the Boat boxes (after the current harvest round; uses Codex/free-model quota).
- [ ] Port check against the Conjectures.io `v4.35.0-rc2` bundle for any passing proof.
- [ ] Wallet: owner-only steps above.
