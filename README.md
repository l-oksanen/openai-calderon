# openai-calderon

Comparator challenge for the main theorem of *Smooth anisotropic uniqueness in the
Calderón problem from one boundary patch* (OpenAI, September 24, 2026), specialized to
`n = 3`, `M` the closed unit ball, `Γ = ∂M`, and metrics Euclidean outside a ball of
radius `1 - ε`.

- Statement: `ComparatorChallenges/AnisotropicCalderon.lean`
- Comparator config: `ComparatorChallenges/AnisotropicCalderon.json`

```sh
lake exe cache get
lake build
```
