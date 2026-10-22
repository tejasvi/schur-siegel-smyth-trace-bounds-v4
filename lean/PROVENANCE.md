# Provenance of shared and adapted files

Several modules are shared with companion formalizations from the same project. Each is listed with its sha256 in this
release. Where the shared original differs from the file here, its sha256 is given as well; the two differ only in
comments.

## Core checker library and shared definitions (from the companion formalization of the lower bound for the Mahler measure of totally positive algebraic integers)

| file | sha256 in this release | shared original, if different (comments only) |
|---|---|---|
| AuxCore.lean | c58371a507d64e4f9b1080b21fabe45129075d412ced049f6585ddc7b20015d5 |  |
| AuxCore/Log.lean | 5102bf10e35dd4538da3cdb7ad0afe3aa0ba8017e9b0791a377e6b9b7868a7eb |  |
| AuxCore/LogK.lean | 2050f3f8ba15b4d33f0a6cbf76ef38955c7399c6b708b8325ac0f559dcb14d9c |  |
| AuxCommon/Basic.lean | c22e3ab3a7d7ac381d7e597fc50b21cf69fe32ff27d8dff259bd133d35f0722d |  |
| AuxCommon/LogSound.lean | 3c8d46ee9155df89a794a061a1e0bc792b7bfb688e9f53f0f9f45dec5da7a546 |  |
| AuxCommon/LogKSound.lean | 990e2cb195f513bc0047f25f9d53fd1fcdc5df670d96a85a3e7acd1e77dd8fe4 |  |
| AuxCommon/Averaging.lean | 4af73b6b03a68a432795146c712c80f4f7e2ae82ed676439b6e7e75ded18bb28 |  |
| AuxCommon/Resultant.lean | ae925f1df8cd6acc1471abaae067b51a9e880a0f75799defdc48dd347f04893d | 734f163db77d375e8a50000d5a8840abfaa1125a527c6bd50606a91c63a1414b |
| AuxCommon/Northcott.lean | 2a5840b80cdf090982ede73648f95980297042abee89e6c55fc4bf1d73eae87d | 2b37720bc2235b5ba31e95c9357fd220bde8cec56cb0ccbb5dddb3ead33b0b1f |

## Potential theory: energy smoothing and the minimum principle (shared modules)

| file | sha256 in this release | shared original, if different (comments only) |
|---|---|---|
| AuxCommon/EnergyProof.lean | 8c283ad491a1f35b1a58b16a0015dd5ecf73f179097464f7c2f107f9cc111f13 |  |
| AuxCommon/Energy/Kernel.lean | 4f4147bb6804bb1878ec3645363f2f0ec82b14d94e669a8b7f0c24c450715c99 |  |
| AuxCommon/Energy/Gauss.lean | ffb73d83a8222e4e5b8113397c50e63499e3e27bd3e31227e78c35cbf1975b6e |  |
| AuxCommon/Energy/PosDef.lean | 4320b1be213bf4a9c3f910ef85b091477d251f819914e366c762e89703a2f318 |  |
| AuxCommon/Energy/Circle.lean | 2ad579559d159db60b19e2e580abc94a8c256c24e6045be03a5686858349b537 |  |
| AuxCommon/Energy/Nu.lean | 7bbdcb43ad23c480856bdbc6303bc2ab65b2d0348f6c49a177a31e85c18545d9 |  |
| AuxCommon/Energy/MinPrinciple.lean | 44705d812585cb7c5dad63aaba287565cdc5d90ff3e8b1a0fbbdb26b73dae360 |  |
| Trace86/MinPrincipleProof.lean | 9aa56011017cae965fdbc0f20d5f89869c46e31fc026accfa62468e6ddd9b8e3 | 15f83a0f53318ad69bc2300b7d07196c73373626ec555b512a9bda6674d30501 |

## Upper bound: arcsine measure, continuity of potentials, integrality, and the step from a measure to infinitely many algebraic integers (shared modules)

| file | sha256 in this release | shared original, if different (comments only) |
|---|---|---|
| AuxCommon/Energy/Arcsine.lean | 5a6c788e0a270830fc64554a6a014b7f2b98bdeef60b0c452f37d9de5459cc0a |  |
| AuxCommon/Energy/Continuity.lean | d7f3a41591e1c512e36284861960ccc99a8cee8f3bcf5174e9b6d0cd9a9bea0c |  |
| AuxCommon/Energy/PotentialSum.lean | 79c537fe2df0c8f5e4fa019e31cf59da6d777df7b61be2cc598cd66055f22e15 | c9d26fa026a28aef917c550c3c8685117f1353cf633fceaf1c19265bcae51254 |
| AuxCommon/RootSum.lean | 2edabffb6965434224595df0d3d7d41aef7b91d8e2b75899a99baf8a7572ef79 |  |
| Trace86/Arcsine.lean | ad6c4dc26f5597614f6f3b57a42091b5de25664a0bb4247f1e6107c61c8c86d9 | c040ccb3fa30d72c0e609afd75609738975c60bce6e8f6c908cc642051374528 |
| AuxCommon/Integrality.lean | 4df343f665f59b4af8d206d7ada718e3f7e9a579e794c0d9ea360b22ccb7cd91 |  |
| Trace86/TraceUpper.lean | d4112a05e10ee2da8d8ffb0c8697216c2dc7a4e2b6a3a1252cee03cc348026f2 |  |

## Adapted files

The checker and its soundness proofs are adapted from the companion Mahler-measure formalization. The namespaces were
renamed (TPMahler to Trace86, TPCore to T86Core, TPN to T86N), and the main term and the tails were changed.

- **Lean files adapted for the lower bound:**
  - in `Trace86/`: Measure, ClosedForm, Reduction (trace version), Assembly (trace version), CertDefs, PolySound,
    AnaSound, TailSound, CheckSound, CheckSound2 to CheckSound10, EnergySound, CertData, and TailSound2 (tails rewritten);
  - `T86Core/Check.lean`.
- **Python tools:** `tools/t86_check_ref.py`, `tools/t86_roots.py` and `tools/gen86_*.py`.
- **Changes from the Mahler-measure checker:**
  - main term x instead of log⁺ x;
  - a constant λ;
  - the slope jumps of unit-mass hat functions, computed exactly;
  - decimal scale 10^12;
  - polynomials of weight zero dropped;
  - a right tail for x - κ log x;
  - no degree budget.
- **Upper bound:** `T86UCore/`, `Trace86U/` and `tools/*86u*` are forks of the lower-bound files. They add:
  - records for the potential of μ_0;
  - the root brackets and moments of condition (M);
  - the irreducibility check, the budget (S) and the trace (T).
- **Written for this project:** `Trace86/HatGen.lean`, `Trace86U/HatGen.lean` and the soundness files listed in
  `STATEMENTS.md`.
- **Kernel-only proof of the upper bound:** `T86UCore/Lits.lean`, `T86UK/` and
  `Trace86U/{LeavesKGen, LeavesKG/, LeavesK, UpperK, AxiomsUK}`, with their generators in `tools/`. They were written for
  this project and follow the design of the companion formalizations' kernel tracks: a literal checker context checked by
  the kernel and small tiling modules.
- **Kernel-only proof of the lower bound:** `T86Core/Lits.lean`, `T86K/`, `T86KE/`, `T86KL/` and
  `Trace86/{EnergyKLemmas, EKR*, EnergyK, LeavesKGen, LeavesKG/, LeavesK, LowerK, AxiomsK}`, with their generators in
  `tools/`, written for this project on the same design; the energy chunks follow the literal-record design of the
  companion kernel tracks.
- **The end-point form of the chord check:** `T86Core/CheckE.lean` and `Trace86/CheckSoundE1.lean` to
  `CheckSoundE5.lean`, written for this project (`STATEMENTS.md` § 5.1). The recursor-level integer operations of
  `epStepKA` (`isnnK`, `iaddK`, `imulK`, `bleK`, `bselK` and their relatives) follow the companion fixed-point kernel
  arithmetic module (KernelArith v2); here they are core-Lean copies, proved equal to the core operations in
  `T86Core/CheckE.lean`. `Trace86/CheckSoundE4.lean` reuses the proof of `chordLB_sound` (`Trace86/CheckSound8.lean`)
  with the node pass replaced.
- **Certificate preparation:** `tools/prep86_cert.py` (written for this project) puts the published lower-bound
  certificate on the checker's node grid (see `STATEMENTS.md` § 8).
