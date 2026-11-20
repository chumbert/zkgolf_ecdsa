#!/usr/bin/env python3
"""Emit Solution/Projected/Certs/Certs*.lean: literal affine-step certificates for
the P-256 fixed-base table, the shift point, and small multiples of G.

Each point is a def with a `decide`-proved curve equation; each step is a
`decide`-proved add/double certificate turned into a group equation by
Solution.Projected.Math.CertSteps, plus a scalar equation `name = k • G`.
Do not edit generated files by hand.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from p256_reference import p, n, G, mul

N_H = 1050          # offset-candidate count (>= 1040); bound 4 * N_H = 4200
BOUND = 4 * N_H
CHUNK = 400         # blocks per generated file
TAIL_CHUNK = 700    # lines per tail file


def fmt(v):
    return hex(v)


def dbl(P):
    x, y = P
    l = (3 * x * x - 3) * pow(2 * y, -1, p) % p
    X = (l * l - 2 * x) % p
    Y = (l * (x - X) - y) % p
    return (X, Y), l


def addp(P, Q):
    x, y = P
    u, v = Q
    assert x != u
    l = (v - y) * pow(u - x, -1, p) % p
    X = (l * l - x - u) % p
    Y = (l * (x - X) - y) % p
    return (X, Y), l


def main():
    outdir = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                          "..", "Solution", "Projected", "Certs")
    os.makedirs(outdir, exist_ok=True)
    for f in os.listdir(outdir):
        os.remove(os.path.join(outdir, f))

    blocks = []   # each block: self-contained point defs + step lemma + scalar lemma
    names = {}    # point tuple -> def name
    scal = {}     # def name -> scalar k with name = k • G
    counter = [0]

    def fresh(prefix):
        counter[0] += 1
        return f"{prefix}{counter[0]}"

    def point_block(P, name):
        names[P] = name
        return [
            f"def {name}_x : K := {fmt(P[0])}",
            f"def {name}_y : K := {fmt(P[1])}",
            f"lemma {name}_curve : {name}_y^2 = {name}_x^3 + params.a*{name}_x + params.b := curve_of_nat (by decide)",
            f"def {name} : W.Point := pt {name}_x {name}_y {name}_curve",
        ]

    def add_block(A, B, R, l, name):
        blk = point_block(R, name)
        blk.append(f"lemma {name}_eq : {name} = {A} + {B} :=")
        blk.append(f"  add_step (l := ({fmt(l)} : K)) {A}_curve {B}_curve {name}_curve (by decide) (by decide) (by decide) (by decide)")
        k = scal[A] + scal[B]
        blk.append(f"lemma {name}_scalar : {name} = ({k} : ℕ) • G := by")
        blk.append(f"  rw [{name}_eq, {A}_scalar, {B}_scalar]; exact (add_smul _ _ G).symm")
        scal[name] = k
        blocks.append(blk)

    def double_block(A, R, l, name):
        blk = point_block(R, name)
        blk.append(f"lemma {name}_eq : {name} = 2 • {A} :=")
        blk.append(f"  double_step (l := ({fmt(l)} : K)) {A}_curve {name}_curve (by decide) (by decide) (by decide) (by decide)")
        k = 2 * scal[A]
        blk.append(f"lemma {name}_scalar : {name} = ({k} : ℕ) • G := by")
        blk.append(f"  rw [{name}_eq, {A}_scalar]; exact (mul_smul 2 _ G).symm")
        scal[name] = k
        blocks.append(blk)

    # G itself
    gname = "cG"
    blocks.append([
        f"def {gname}_x : K := params.gx",
        f"def {gname}_y : K := params.gy",
        f"lemma {gname}_curve : {gname}_y^2 = {gname}_x^3 + params.a*{gname}_x + params.b := generator_eq",
        f"def {gname} : W.Point := pt {gname}_x {gname}_y {gname}_curve",
        f"lemma {gname}_scalar : {gname} = (1 : ℕ) • G := rfl",
    ])
    names[G] = gname
    scal[gname] = 1

    # B[i] = 4^i G via two doublings; T[i][d] = (4+d) 4^i G
    B = [G]
    tab = {}
    for i in range(128):
        d1 = dbl(B[i])
        double_block(names[B[i]], d1[0], d1[1], fresh("cD"))
        d1name = names[d1[0]]
        d2 = dbl(d1[0])
        double_block(d1name, d2[0], d2[1], fresh("cB"))
        B.append(d2[0])
        d2name = names[d2[0]]
        tab[(i, 0)] = d2name
        dB = {1: B[i], 2: d1[0]}
        if 3 not in dB:
            t3 = addp(d1[0], B[i])
            add_block(d1name, names[B[i]], t3[0], t3[1], fresh("cT3"))
            dB[3] = t3[0]
        for d in (1, 2, 3):
            R, l = addp(B[i + 1], dB[d])
            add_block(d2name, names[dB[d]], R, l, fresh("cT"))
            tab[(i, d)] = names[R]

    # shift = sum_{i=0}^{127} B[i+1]
    sprev, sname = B[1], names[B[1]]
    for i in range(1, 128):
        R, l = addp(sprev, B[i + 1])
        add_block(sname, names[B[i + 1]], R, l, fresh("cS"))
        sprev, sname = R, names[R]
    shift_name = sname
    assert sprev == mul(4 * ((4**128 - 1) // 3), G)

    # small multiples kG[m] = m G, m = 1..BOUND-1
    kG = {1: G}
    kname = {1: gname}
    for m in range(2, BOUND):
        if kG[m - 1] == G:
            R, l = dbl(G)
            double_block(gname, R, l, fresh("cK"))
        else:
            R, l = addp(kG[m - 1], G)
            add_block(kname[m - 1], gname, R, l, fresh("cK"))
        kG[m] = R
        kname[m] = names[R]

    # tail, split into parallel groups that all import the last chunk directly
    # (chained tail files serialize the build), plus one final assembler file
    tab_lemmas = []
    tab_entries = sorted(tab.items())
    # First 43 pairs go to CertsTab0, use NEW proof technique (pilot-only rollout per S4)
    # Remaining pairs keep OLD technique to preserve byte-identical output for other files
    for idx, ((i, d), tname) in enumerate(tab_entries):
        tab_lemmas.append(f"lemma tab_{i}_{d} : tableX {i} {d} = {tname}_x ∧ tableY {i} {d} = {tname}_y := by constructor <;> rfl")
        if idx < 43:  # First 43 pairs for CertsTab0
            tab_lemmas.append(f"lemma tab_pt_{i}_{d} : ∃ h, pt (tableX {i} {d}) (tableY {i} {d}) h = ((4 + {d}) * 4^{i}) • G := by")
            tab_lemmas.append(f"  use {tname}_curve; show pt (tableX {i} {d}) (tableY {i} {d}) {tname}_curve = _; show pt {tname}_x {tname}_y {tname}_curve = _; exact {tname}_scalar")
        else:  # Rest use OLD technique
            tab_lemmas.append(f"lemma tab_pt_{i}_{d} : ∃ h, pt (tableX {i} {d}) (tableY {i} {d}) h = ((4 + {d}) * 4^{i}) • G :=")
            tab_lemmas.append(f"  ⟨{tname}_curve, by rw [tab_{i}_{d}.1, tab_{i}_{d}.2]; exact {tname}_scalar⟩")
    kG_lemmas = []
    for m in range(1, BOUND):
        kG_lemmas.append(f"lemma kG_ne_{m} : ({m} : ℕ) • G ≠ 0 := fun h => pt_ne_zero {kname[m]}_curve ({kname[m]}_scalar.trans h)")
    final = []
    final.append("theorem table_pt_aux : ∀ (i : Fin 128) (d : Fin 4), ∃ h, pt (tableX i d) (tableY i d) h = ((4 + d.val) * 4^i.val) • G := by")
    final.append("  intro i d")
    final.append("  fin_cases i <;> fin_cases d")
    for i in range(128):
        for d in range(4):
            final.append(f"  · exact tab_pt_{i}_{d}")
    final.append(f"lemma shift_pt_aux : ∃ h, pt shiftX shiftY h = (4 * ((4^128 - 1) / 3)) • G :=")
    final.append(f"  ⟨{shift_name}_curve, by rw [show shiftX = {shift_name}_x from rfl, show shiftY = {shift_name}_y from rfl]; exact {shift_name}_scalar⟩")
    final.append("theorem small_multiples_ne_zero_aux : ∀ m : ℕ, 0 < m → m < 4 * 1050 → m • G ≠ 0 := by")
    final.append("  intro m hm _")
    final.append("  have h : ∀ fm : Fin 4200, 0 < fm.val → fm.val • G ≠ 0 := by")
    final.append("    intro fm hpos")
    final.append("    fin_cases fm")
    final.append("    · exact absurd hpos (by simp)")
    for m in range(1, BOUND):
        final.append(f"    · exact kG_ne_{m}")
    final.append("  exact h ⟨m, by omega⟩ hm")

    footer = "\nend Solution.Projected\n"
    opts = "set_option maxRecDepth 1000000\nset_option maxHeartbeats 8000000\n"
    nfiles = (len(blocks) + CHUNK - 1) // CHUNK
    for fi in range(nfiles):
        imp = "Solution.Projected.Math.CertSteps" if fi == 0 else f"Solution.Projected.Certs.Certs{fi-1}"
        header = (f"import {imp}\nimport Solution.Projected.Constants\n\n"
                  "/-! Generated by scripts/gen_projected_certs.py. Do not edit. -/\n"
                  f"{opts}"
                  "namespace Solution.Projected\n\nopen Challenge.Specs.ECDSAP256\n\n")
        chunk = [l for b in blocks[fi * CHUNK:(fi + 1) * CHUNK] for l in b]
        with open(os.path.join(outdir, f"Certs{fi}.lean"), "w") as f:
            f.write(header + "\n".join(chunk) + footer)

    last_chunk = f"Solution.Projected.Certs.Certs{nfiles - 1}"

    def write_group(prefix, lines, chunk_size):
        n = (len(lines) + chunk_size - 1) // chunk_size
        for k in range(n):
            header = (f"import {last_chunk}\nimport Solution.Projected.Constants\n\n"
                      "/-! Generated by scripts/gen_projected_certs.py. Do not edit. -/\n"
                      f"{opts}"
                      "namespace Solution.Projected\n\nopen Challenge.Specs.ECDSAP256\n\n")
            content = header + "\n".join(lines[k * chunk_size:(k + 1) * chunk_size])
            # Add blank line before footer for CertsTab0 to match verified file (S4 pilot)
            if prefix == "CertsTab" and k == 0:
                content += "\n"
            content += footer
            with open(os.path.join(outdir, f"{prefix}{k}.lean"), "w") as f:
                f.write(content)
        return n

    ntab = write_group("CertsTab", tab_lemmas, 129)  # multiple of 3: tab+tab_pt pairs never split
    nkg = write_group("CertsK", kG_lemmas, 700)
    imports = [f"import Solution.Projected.Certs.CertsTab{k}" for k in range(ntab)]
    imports += [f"import Solution.Projected.Certs.CertsK{k}" for k in range(nkg)]
    header = ("\n".join(imports) + "\nimport Solution.Projected.Constants\n\n"
              "/-! Generated by scripts/gen_projected_certs.py. Do not edit. -/\n"
              f"{opts}"
              "namespace Solution.Projected\n\nopen Challenge.Specs.ECDSAP256\n\n")
    with open(os.path.join(outdir, "CertsFinal.lean"), "w") as f:
        f.write(header + "\n".join(final) + footer)
    print(f"wrote {nfiles} chunk files + {ntab} tab + {nkg} kG + 1 final, {len(blocks)} blocks to {outdir}")


if __name__ == "__main__":
    main()
