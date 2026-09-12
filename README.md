# formal-gdt

## Background

GD&T has been in use by engineers and manufacturers for over 85 years. It is a precise, standardized symbolic language for communicating how much a manufactured part is allowed to vary from its original, intended design.

For example, you might annotate a line in your design with the following GD&T:

```
│ ─ │ 0.05 │
```

This means that the indicated surface line element must lie within a straightness zone with tolerance 0.05.

The units are not specified by the GD&T symbol itself; they depend on the drawing or specification. The geometric definitions underlying these requirements are made rigorous in ASME Y14.5.1.

For example, Y14.5.1 defines the straightness zone for a derived median line as a cylindrical zone whose diameter is the specified tolerance.

## So why formalise GD&T?

There are a few reasons.

- The underlying mathematics is already precise.
- GD&T involves many interacting geometric definitions, which are hard to keep track of.
- The mathematics is difficult to read and verify manually.

Formalisation gives us a way to turn these definitions into objects and propositions that can be checked mechanically.

## Project

I formalise the main definitions, "theorems", and best practices of ASME Y14.5 using Lean.

I put "theorems" in quotes here because Y14.5 is an engineering standard, not a mathematical text. So instead of theorems, there are mathematical practices that engineers must follow.

For example, one simple mathematical practice is the fastener formula which tells you the maximum positional tolerance (T) you're allowed to give to a hole when using a fastener (screw, bolt, nut, washer, etc.).

```
T = H - F
```

Where H = diameter of the hole and F = diameter of the fastener.

By formalising in Lean, we're able to show formally, under what cases, this formula holds and when it doesn't.
