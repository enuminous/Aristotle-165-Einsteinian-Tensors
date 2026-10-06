# Summary of changes for run ae025faf-c2ad-4438-a30b-43b825cda9c6
**Answer:** the repository names **4 new potential laws** and proposes no new law of nature. In `THEOREM_REGISTER.md` (`main` at 3a5b659) they are listed under "Candidate consistency laws":

- **FS-C01, Projected Atlas Gluing.** No longer just a candidate: it is now a proved mathematical theorem in the companion repository `EFMW_Post156_Zoo_Audit`.
- **FS-C02, Master-Action Reciprocity.** Still a candidate.
- **FS-C03, Noether/Conservation Closure.** Still a candidate.
- **FS-C04, Parameter Economy.** Still a candidate.

So 4 in total, 3 still open (C02–C04). The register says outright "No new fundamental physical law claimed". FS-T08, the "Trilinear Null-Slice Law", has "law" in its name, but the register labels it ordinary algebra, not a new law.

**What I verified:**
1. **The repo's own Lean files** build cleanly with no `sorry`. They are copied into `RequestProject/Upstream/`. However, most of them only check plain arithmetic (for example `Nat.choose 11 3 = 165`, `8 = 8`, `1 = 1`) and don't say anything about actual sets of sectors.
2. **My own proofs of FS-T01 to FS-T07**, in `RequestProject/Verified.lean`, are stated about the 11 actual sectors and all their 3-element subsets. Every claim checks out:
   - 165 triplets;
   - each sector is in 45 of them;
   - each pair of sectors is in 9;
   - the six classes have sizes 56/56/28/16/8/1 and cover every triplet;
   - 585 equation statements;
   - deleting any \(k\) sectors leaves \(\binom{11-k}{3}\) triplets;
   - triplet pairs overlap in 2, 1 or 0 sectors 1980, 6930 and 4620 times, out of 13530 pairs.
   
   The same file also proves the simplest form of FS-C02: a term \(\lambda\varphi_i\varphi_j\) gives the same coefficient in both field equations. The build has no `sorry`. The finite counts are checked with `native_decide`.
3. **FS-C01:** I built the companion repository (and its pinned dependency) locally. `fieldSpace_projected_atlas_gluing` and `projected_atlas_gluing_unique` build with no `sorry` and rely only on Lean's standard axioms. The theorem holds under its stated condition that each equation component involves at most 3 sectors. That repository is not part of this project.
4. **The equation file:** the repo's audit script reports 165 complete blocks and 45 + 90 + 90 + 360 = 585 statements. This is a script result only, not proved in Lean.

**Observations from scripts only (not proved in Lean):**
- The source writes the scalar pair couplings in both directions as separate symbols (\(\lambda_{ij}\) and \(\lambda_{ji}\)), giving 56. If FS-C02 holds, they reduce to 28.
- There are 550 distinct \(\lambda\)/\(\kappa\) coupling symbols, which is the parameter count FS-C04 aims to reduce.
- FS-C03 and FS-C04 can't be tested yet, because the source doesn't define the mixed interaction terms (`T^(int)`, `Ξ`), the gauge groups, or units.

Full details are in `FIELDSPACE_VERIFICATION.md`.