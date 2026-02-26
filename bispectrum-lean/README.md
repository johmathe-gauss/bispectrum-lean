# bispectrum-lean

Lean 4 formal proofs for the G-bispectrum: a group-invariant signal descriptor
used in equivariant neural networks.

This repository accompanies the paper on efficient G-bispectrum computation
and provides machine-checked proofs of the core mathematical claims.

## What is the bispectrum?

For a function $f : G \to \mathbb{C}$ on a group $G$, the bispectrum is a
collection of invariants $B[f](\rho_1, \rho_2)$ built from products of Fourier
coefficients. The key property:

$$B[L_g f] = B[f] \quad \forall g \in G$$

where $L_g f(x) = f(g^{-1} x)$ is the left translation. The bispectrum is
also *complete*: it separates orbits, meaning $B[f] = B[h]$ iff $f$ and $h$
are in the same $G$-orbit.

## Proof targets

| Theorem | Group | Status |
|---------|-------|--------|
| DFT shift lemma (`dft_cycShift`) | $\mathbb{Z}/n$ | `sorry` stub |
| Conjugate/negative shift lemma (`dft_cycShift_neg`) | $\mathbb{Z}/n$ | `sorry` stub |
| $C_n$ bispectrum invariance | $C_n$ | `sorry` stub |
| $C_n$ bispectrum completeness | $C_n$ | `sorry` stub |
| Finite-group Fourier equivariance | finite $G$ | `sorry` stub |
| $D_n$ bispectrum invariance | $D_n$ | placeholder theorem |
| General finite group invariance | finite $G$ | placeholder theorem |

## Repository structure

```
bispectrum-lean/
├── lean-toolchain          # Pins Lean 4 version
├── lakefile.toml           # Lake build config (Mathlib dependency)
├── Bispectrum.lean         # Root module
├── scripts/
│   └── sorry_count.sh      # Count `sorry` occurrences in project files
└── Bispectrum/
    ├── DFT.lean            # DFT on ZMod n, cyclic shift lemmas
    ├── Cyclic.lean         # C_n bispectrum + invariance/completeness stubs
    └── FiniteGroup.lean    # General finite-group framework + stubs
```

## Getting started (Ubuntu 24.04)

### 1. Install elan (Lean version manager)

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/main/elan-init.sh | sh -s -- -y
source ~/.bashrc   # or restart your terminal
```

### 2. Clone and build

```bash
git clone https://github.com/johmathe-gauss/bispectrum-lean
cd bispectrum-lean

# Download pre-compiled Mathlib binaries (saves hours of compilation)
lake exe cache get

# Build the project
lake build
```

This will take a few minutes on first run (downloading Mathlib cache).

### 3. Editor setup

**Emacs** (recommended):
```bash
# Install lean4-mode via MELPA
M-x package-install RET lean4-mode RET
```

**Neovim**:
```bash
# Install lean.nvim via your plugin manager, e.g. lazy.nvim:
{ 'Julian/lean.nvim', dependencies = { 'neovim/nvim-lspconfig', 'nvim-lua/plenary.nvim' } }
```

**CLI only** (check proofs without an editor):
```bash
lake build 2>&1 | grep -E "error|warning|sorry"
```

Count remaining `sorry` placeholders in this repo:
```bash
./scripts/sorry_count.sh
```

### 4. Learning Lean 4

- [Natural Number Game](https://adam.math.hhu.de/) — interactive intro, no install needed
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) — comprehensive textbook
- [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/) — searchable API

## Key mathematical ideas

### DFT shift lemma

The DFT of the cyclic shift $T_g f$ (where $(T_g f)(x) = f(x-g)$) satisfies:

$$\widehat{T_g f}(k) = e^{-2\pi i g k / n} \cdot \hat{f}(k)$$

This is the spectral version of translational equivariance.

### Bispectrum phase cancellation

Define $B[f](k_1, k_2) = \hat{f}(k_1) \cdot \hat{f}(k_2) \cdot \overline{\hat{f}(k_1+k_2)}$.

Under a shift by $g$:
$$B[T_g f](k_1, k_2) = \underbrace{e^{-2\pi i g k_1/n} \cdot e^{-2\pi i g k_2/n} \cdot e^{+2\pi i g(k_1+k_2)/n}}_{=\,1} \cdot B[f](k_1, k_2)$$

The exponents sum to $g(k_1 + k_2 - (k_1+k_2))/n = 0$ in $\mathbb{Z}/n\mathbb{Z}$.

## Contributing

Fill in the `sorry` stubs! Each `sorry` has a comment explaining the
proof strategy. Good first target: `dft_cycShift` in `Bispectrum/DFT.lean`.

## License

MIT
