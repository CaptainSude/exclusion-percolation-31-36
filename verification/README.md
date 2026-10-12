# Verification record

[Repository](../README.md) · [Reproduce the check](../docs/verification.md) · [Literature inputs](../docs/literature.md)

| Record | Contents |
| --- | --- |
| [status.json](status.json) | Successful build, pinned versions and SHA256 hashes of all 443 Lean sources |
| [full-build.log](full-build.log) | Full build output and exhaustive transitive axiom audit |
| [Standalone Lean archive](nearest-neighbor-31-36-lean.zip) | The original checked Lean package, including its detailed source notes |

The recorded check completed on **12 October 2026 at 14:54 UTC**. It built **3,767 jobs** and audited **8,241 declarations**, including **6,231 theorems**. Its permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The original records and archive are preserved byte for byte. The current repository supplies the same 443 Lean source files. New runs of `Verify.ps1` write to `verification/local/`, keeping this completed record intact.

The archive's SHA256 is:

```text
149f867bc3f16682b07c8448752ebf885f2d6759c6daa99561d7b1feb858d481
```
