# List.length_append



---

## Statement

```lean

```

## Explanation

We prove by induction that the length of concatenated lists equals the sum of their individual lengths. This fundamental property connects list operations with arithmetic and demonstrates the power of structural induction.

## Visual Proof

[![Animation](demo_export_proof_diagram.png)](demo_export_proof_diagram.png)


## Proof Steps

### Step 1: Base case: empty list

$$([] ++ l2).length = [].length + l2.length$$



### Step 2: Simplify the base case

$$l2.length = 0 + l2.length$$



### Step 3: Inductive step: cons case

$$((h :: t) ++ l2).length = (h :: t).length + l2.length$$



### Step 4: Expand the cons case

$$(h :: (t ++ l2)).length = (1 + t.length) + l2.length$$



### Step 5: Apply induction hypothesis

$$1 + (t ++ l2).length = 1 + t.length + l2.length$$



### Step 6: Substitute induction hypothesis

$$1 + (t.length + l2.length) = 1 + t.length + l2.length$$



### Step 7: Apply associativity of addition

$$(1 + t.length) + l2.length = 1 + t.length + l2.length$$






---

_Generated on 2025-07-07T23:40:52.058819_
