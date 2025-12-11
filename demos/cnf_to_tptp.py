#!/usr/bin/env python3
"""Convert DIMACS CNF to TPTP CNF format for Vampire/E prover"""
import sys

def dimacs_to_tptp(filename):
    clauses = []
    with open(filename) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c') or line.startswith('p') or line.startswith('%'):
                continue
            lits = [int(x) for x in line.split() if x != '0']
            if lits:
                clauses.append(lits)

    # Output TPTP CNF format
    for i, clause in enumerate(clauses):
        tptp_lits = []
        for lit in clause:
            if lit > 0:
                tptp_lits.append(f"p{lit}")
            else:
                tptp_lits.append(f"~p{abs(lit)}")
        clause_str = " | ".join(tptp_lits)
        print(f"cnf(c{i}, axiom, ({clause_str})).")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: cnf_to_tptp.py <file.cnf>", file=sys.stderr)
        sys.exit(1)
    dimacs_to_tptp(sys.argv[1])
