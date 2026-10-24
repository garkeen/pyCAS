"""Language: sorts, the structural signature, typing and problem specifications.

This layer turns pure syntax into meaningful expressions. It knows the language's
own structure (arithmetic, comparison, logic, binding) and nothing about concrete
mathematical functions, which are declared data. It also provides a data-only
declaration language for binder and operator signatures.
"""
