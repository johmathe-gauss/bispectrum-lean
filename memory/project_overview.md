# Bispectrum Project Overview

## Goal
Build a Python module for efficient computation of the G-Bispectrum on groups, focusing on making bispectra complete while selective (more efficient).

## Repository
- **Location**: https://github.com/geometric-intelligence/bispectrum/ (private)
- **Status**: Initial version available, needs GitHub access setup for Gauss

## Key Mathematical Framework

### The Problem
Traditional G-invariant layers in neural networks are either:
- **Incomplete** (max/avg pooling): lose too much information
- **Complete but expensive** (G-TC, full G-Bispectrum): O(|G|²) or O(|G|³) complexity

### The Solution: Selective G-Bispectrum
- **Core insight**: Full bispectrum has redundancies
- **Reduction**: O(|G|²) coefficients → O(|G|) coefficients
- **Completeness**: Still recoverable via inversion
- **Complexity**: O(|G|log|G|) with FFT

### Reference Paper
"The Selective G-Bispectrum and its Inversion: Applications to G-Invariant Networks"
- arXiv: 2407.07655v2
- Authors: Mataigne, Mathe, Sanborn, Hillar, Miolane
- Local copy: `/workspace/group/selective_g_bispectrum.pdf`
- LaTeX source: `/workspace/group/neurips_2024.tex`

## Groups of Interest
1. **Cyclic groups** C_n (rotations)
2. **Dihedral groups** D_n (rotations + reflections) — most important for 2D
3. **Commutative groups** (all finite ones proven complete)
4. **Octahedral groups** O, FO (3D symmetries)
5. **SO(3), O(3)** (continuous rotation groups) — future target

## Current Status
- Paper understood ✓
- Math foundations documented ✓
- Need GitHub access
- Need colleague's draft on bispectra for various groups

## Next Steps
1. Get GitHub access to private repo
2. Review current implementation
3. Identify bottlenecks and missing pieces
4. Implement/optimize as needed
