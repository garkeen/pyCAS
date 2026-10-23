"""Semantics: frames, elaboration, definitions and algebra bridges.

This layer turns pure syntax into meaningful objects: it owns the name
environment (`frames`), alias expansion, the translation between terms and
parent elements, the explicit algebra request that fixes coefficient, parameter
and target roles, and the choice of a derivation. It imports the language and
algebra layers; it does not import the kernel store or any workflow.
"""
