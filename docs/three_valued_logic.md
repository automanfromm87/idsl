# Missing values and three-valued logic

> **TL;DR** — when a field is `missing`, comparisons and boolean
> operations return `missing`, not `false`. Rules with `missing`
> predicates *do not fire*. Use `is missing` / `is present` to
> probe for the field's existence explicitly.

## Why this exists

In a contract-review or compliance setting, "we don't know yet" is
fundamentally different from "the answer is no":

- **No data**: `LiabilityCap` not provided → we *don't know* whether
  the cap is high or low. We should *not* take an action that assumes
  it's low.
- **Negative answer**: `LiabilityCap = $0` → we *know* there's no cap.
  We can act on that knowledge.

Two-valued boolean logic conflates the two. Three-valued logic keeps
them separate.

## The truth tables

`missing` is a third truth value alongside `true` and `false`. The
operators handle it like SQL handles `NULL`:

### Comparisons

Any comparison with a `missing` operand yields `missing`:

| expression                    | result    |
| ----------------------------- | --------- |
| `Cap > 100` when `Cap missing` | `missing` |
| `Cap == 0`  when `Cap missing` | `missing` |
| `Cap != 0`  when `Cap missing` | `missing` |
| `Cap is missing`              | `true`    |
| `Cap is present`              | `false`   |

`is missing` and `is present` are the **only** way to get a plain
boolean answer about whether a value is set.

### Negation

| expression       | result    |
| ---------------- | --------- |
| `not true`       | `false`   |
| `not false`      | `true`    |
| `not missing`    | `missing` |

This is the part that surprises people. **`not (Cap > 100)`** when
`Cap` is missing is **not** `true` — it's `missing`. Using `not` to
"flip" a comparison does not coerce missing into a boolean.

### Conjunction (`and`) — Kleene table

| `a` \ `b`  | `true`    | `false`   | `missing` |
| ---------- | --------- | --------- | --------- |
| `true`     | `true`    | `false`   | `missing` |
| `false`    | `false`   | `false`   | `false`   |
| `missing`  | `missing` | `false`   | `missing` |

`false` short-circuits even when the other side is `missing`.

### Disjunction (`or`) — Kleene table

| `a` \ `b`  | `true`    | `false`   | `missing` |
| ---------- | --------- | --------- | --------- |
| `true`     | `true`    | `true`    | `true`    |
| `false`    | `true`    | `false`   | `missing` |
| `missing`  | `true`    | `missing` | `missing` |

`true` short-circuits even when the other side is `missing`.

### `if` expressions

`if missing then T else E` is `missing`, not `E`. The branch isn't
chosen because the condition didn't reach a definite truth value.

## How rules behave

A rule's `when:` block requires every predicate to be `true`. A
predicate that evaluates to `missing` counts as not-fulfilled — the
rule does **not** fire. This is the conservative default: don't act
on incomplete data.

```
schema Order:
  - Cap: Money

rule too_costly on Order:
  when:
    Cap > $100             # missing → missing → rule skipped
  then:
    flag("review")
```

If the user submits an Order *without* a `Cap`, `too_costly` does
not flag it. To trigger explicitly on missing data, write:

```
rule too_costly_or_unknown on Order:
  when:
    Cap is missing or Cap > $100
  then:
    flag("review")
```

## The negation pitfall

This is the most common surprise:

```
# WRONG: does NOT flag uncapped contracts.
rule needs_cap on Contract:
  when:
    not (Cap > $0)
  then:
    flag("uncapped — set a limit")
```

Reasoning the writer assumed:
- `Cap` missing → `Cap > $0` is `false` → `not false` is `true` → fires.

What actually happens:
- `Cap` missing → `Cap > $0` is `missing` → `not missing` is `missing`
  → rule does not fire.

The fix is to use the explicit probe:

```
rule needs_cap on Contract:
  when:
    Cap is missing
  then:
    flag("uncapped — set a limit")
```

Or, if you want both "missing" and "explicitly set to zero or below":

```
rule needs_cap on Contract:
  when:
    Cap is missing or Cap <= $0
  then:
    flag("uncapped — set a limit")
```

## The summary rule

When you write a rule predicate, ask yourself:
**"What if the field isn't there?"**

- If the answer is "the rule should fire", use `is missing` or
  `is missing or <comparison>`.
- If the answer is "the rule should not fire" (the conservative
  default), do nothing — three-valued logic already handles it.
- Never rely on `not <comparison>` to flip a missing into a true.

## Why not just default to `false`?

Because two-valued logic loses information at the worst time. A
half-filled-in contract that silently passes "is high risk" checks
because every predicate's missing fields coerced to `false` is the
exact failure mode iDSL is designed to prevent.

The cost is one bit of programmer attention: predicates that *should*
treat missing as a flag-worthy condition need to say so explicitly.
The benefit is that incomplete data never causes an action to fire
that the rule author didn't think about.
