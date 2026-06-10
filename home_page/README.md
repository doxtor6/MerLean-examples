# Home Page Folder Memory

## Purpose

`home_page/` is the source for the MerLean public website. It is a lightweight static SPA with tabs for Home, Publications, Demo video, Blogs, and Examples.

## Important Files

- `index.html` is the main SPA source.
- `assets/css/style.css` controls the site design.
- `assets/js/app.js` controls tab navigation, blog metadata, blog rendering, and BibTeX copy behavior.
- `blogs/` stores Markdown blog posts fetched by the SPA.
- `_site/` is a tracked generated/static mirror. Do not treat it as the canonical source.

## Recent History

- 2026-05-27: Updated the homepage with the MerLean-Prover paper, FormalQualBench and Putnam 2025 tables, a new BibTeX entry, a top Publications card with equal-contribution marks, refreshed homepage text/stats, and removal of the old hero "Read the Paper" button.
- 2026-05-27: Local Jekyll was unavailable (`bundle exec jekyll build` asked for `bundle install`), so `_site` was synchronized mechanically from source for the changed homepage files and referenced assets.
- 2026-05-27: Added this folder memory.
- 2026-06-09: Added a public fundraising, advisor, and cofounder-search block to `index.html`, positioned between the About section and MerLean-Prover Results. The source and tracked `_site` mirror were updated manually for local/static serving.
- 2026-06-09: Added a Lean Eval Benchmark result card above the MerLean-Prover FormalQualBench and Putnam tables, linking to `https://lean-lang.org/eval/`, showing the current top 10 submitters, and positioning MerLean-Prover as a small academic-team entry in the top #5/#6 tier by solved count. Updated source and tracked `_site` mirror manually.
- 2026-06-09: Revised the Lean Eval result card into a two-column layout: the top-10 table sits in the left half-width table panel, and the benchmark narrative/link sits on the right. Updated source and tracked `_site` mirror manually.
- 2026-06-09: Adjusted the Lean Eval result card CSS so the left/right layout persists at all preview widths, with the table scrolling inside its left subwindow and clearer spacing before the FormalQualBench and Putnam result cards. Updated source and tracked `_site` mirror manually.
- 2026-06-09: Narrowed and centered the Lean Eval narrative text inside the right panel to improve line breaks while preserving the left/right card layout. Updated source and tracked `_site` mirror manually.
- 2026-06-09: Restyled the fundraising section heading from the purple eyebrow pill to a normal black section heading and removed the separate `MerLean is actively preparing a pre-seed round` headline. Updated source and tracked `_site` mirror manually.
- 2026-06-09: Fixed the top-left nav logo so the rectangular MerLean logo keeps its natural aspect ratio instead of being forced into a 36px square. Updated source and tracked `_site` mirror manually.
- 2026-06-09: Updated the About MerLean stat cards to show two-line purple benchmark values: Lean Eval `21/179 / Top 5/6`, FormalQualBench `10/23 / Top 1`, and Putnam 2025 `12/12, 789 mins / Top 1`, with aligned gray labels across the three cards. Updated source and tracked `_site` mirror manually.
- 2026-06-09: Shortened the About MerLean copy into one verifier/prover paragraph and reduced the purple stat-card value size from `1.8rem` to `1.44rem` (`0.8x`). Updated source and tracked `_site` mirror manually.
- 2026-06-09: Revised the About MerLean wording from `without hallucinated correctness claims` to `without hallucination`. Updated source and tracked `_site` mirror manually.
- 2026-06-09: Reverted the About MerLean final clause to `supports vibe coding without hallucination by grounding generated code in formal checks`. Updated source and tracked `_site` mirror manually.
- 2026-06-10: Added `merlean.prover@gmail.com` as the public contact email in the Home fundraising/recruiting section and again at the bottom of the Home tab. The fundraising contact line sits directly under the fundraising intro sentence, not in a separate mini-card. Updated source and tracked `_site` mirror manually.

## Notes For Future Agents

- Edit `index.html`, `assets/css/style.css`, and `assets/js/app.js` first, then synchronize `_site` if needed.
- For local verification, run `python3 -m http.server <port> --bind 127.0.0.1` from `home_page/` and check `/`, `/assets/js/app.js`, and any changed media/blog assets.
- Avoid putting internal fundraising or diligence material on the public site.
