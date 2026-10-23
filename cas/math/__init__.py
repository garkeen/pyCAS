"""Mathematical operations: specifications, independent verification, checkers.

This layer knows mathematics; it does not write the ledger, choose user focus or
search strategies. Candidate generation and verification live in separate
modules so a checker never certifies its own search.
"""
