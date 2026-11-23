# Survey notes for riemann-masullo, 23 November 2026

Reports written by AI agents while contributing to
[mccorvie/riemann-masullo](https://github.com/mccorvie/riemann-masullo). They are working notes,
kept here so that others can use the pointers. Nothing in them was reviewed by a person.

Issue states (free, claimed, open pull requests) are those of 23 November 2026 between 07:00 and
09:00 UTC and go stale within hours. Each report says what was read in the source and what comes
only from a search result or a README; outside code was read, never built. `<repo>` stands for a
checkout of riemann-masullo and `<notes>/` for the scratch folder of the agents, which is not
published.

| File | Contents |
|---|---|
| [`parallel-formalizations.md`](parallel-formalizations.md) | Other Lean efforts on the same paper and on neighbouring results (`thatnealpatel/grh`, Zeta23 in `anthropics/formal-math`, the mirror of Alpöge's RH submission, `openai/math`, the outside audits): what each is, licence and Lean version, and which of their declarations apply to which open issue here |
| [`lean-ecosystem-sweep.md`](lean-ecosystem-sweep.md) | General Lean libraries and tooling: Tau Ceti, Mathlib open pull requests, smaller projects, search and agent tools for Lean 4.36, how to restore the CI build of `main`, and a list of topics for which nothing was found |
| [`exponential-polynomial-independence.md`](exponential-polynomial-independence.md) | Where a proof of linear independence of `t ↦ t^j exp(z t)` exists, and how to get the continuous statement from the discrete one |
| [`scout-ch05-open-issues.md`](scout-ch05-open-issues.md) | The open proof issues of Ch05 Sec3a, Sec3b, Sec4, Sec5 graded for tractability, with proof sketches for the best ones |
| [`scout-ch07-open-issues.md`](scout-ch07-open-issues.md) | The same for Ch07 Sec2, Sec3a, Sec3b, Sec4, Sec5 |
| [`scout-ch01-ch06-ch10-ch13-open-issues.md`](scout-ch01-ch06-ch10-ch13-open-issues.md) | The same for Ch01 Sec4, Ch06 Sec2–3, Ch10 Sec1 and Sec3, Ch11, Ch12 Sec4, Ch13 Sec3, AppB Sec4b |

Tractability grades in the scout reports: A, the whole proof is visible and is assembly of
existing lemmas; B, plausible in a few hours with one or two steps of real work; C, needs
substantial new theory; F, looks false or vacuous as stated.
