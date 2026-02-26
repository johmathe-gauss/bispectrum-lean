# Current Task

## Status: Codebase Reviewed - Ready for Implementation

### Completed ✓
1. ✓ Papers read and understood (main + draft)
2. ✓ GitHub access obtained (PAT stored securely)
3. ✓ Repo cloned and explored
4. ✓ Implementation analysis complete

### Current Understanding

**What exists**: SO(3) bispectrum implementation (continuous rotations on sphere)
- Working torch module
- Pre-computed CG matrices (lmax=5)
- Good test coverage
- Clean, documented code

**What's missing**: Selective bispectrum for *finite* groups (paper's main contribution)
- Cyclic groups (C_n)
- Dihedral groups (D_n)
- Octahedral groups (O, FO)
- Algorithm 1 (selective coefficient selection)
- Runtime CG computation for finite groups

### Next Steps - Awaiting Direction

**Option A: Optimize SO(3)**
- Implement selective coefficients for continuous case
- Profile and benchmark current implementation
- Add paper's validation experiments

**Option B: Add Finite Groups**
- Start with cyclic groups (simplest)
- Use formulas from colleague's draft
- Implement Algorithm 1
- Add FFT for groups

**Option C: Full Refactor**
- Design unified framework for all groups
- Integrate with escnn for CG matrices
- Implement selective selection across all groups

**Question for Johan**: Which direction should I prioritize?

---
*Last updated: 2026-02-23 03:45 UTC*
