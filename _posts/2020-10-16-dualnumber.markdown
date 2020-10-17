---
layout: post
title:  "The Dual Number Game"
date:   2020-10-17 11:17:00 EDT
categories: math
---

So I've been hearing about theorem provers in general,  and lean + mathlib in particular, 
for a while now, and I thought 'hey, let's try it out.'

(I should say that by mathlib I mean the good people of 
the [Lean Prover Community](https://leanprover-community.github.io/), and also
that I got some help with syntax for this code from Adam Topaz in their 
Zulip channel, for which I am grateful.)

One of the main things they have for getting started is something called 
the [Natural Number Game](https://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/)
and, more interestingly, the [Complex Number Game](https://github.com/ImperialCollegeLondon/complex-number-game).

I starting thinking that doing quaternions might be fun, but some googling showed that
there's already a PR out there for quaternion algebras and it looked a little complicated,
so I decided to fall back to [dual numbers](https://en.wikipedia.org/wiki/Dual_number)
and [split-complex numbers](https://en.wikipedia.org/wiki/Split-complex_number).
 
These are of course variants of the complex numbers $$a+bi$$ where instead
of $$i^2 = -1$$ we have $$i^2 = 0$$ (dual numbers) or $$i^2 = 1$$ (split complex).
If we're doing two we might as well do them all, and while we're at it 
handle arbitrary base rings (as long as they commute).
 
The plan will be to define the numbers, prove some properties, and establish that
they're both a ring and an algebra.
 
So here we go : 
 
    import data.real.basic
    import tactic.simps 
    import algebra.algebra.basic 

    @[ext]
    structure dual_algebra (R : Type*)[comm_ring R] (jj: R) :=
    mk {} :: (re : R) (im : R)
    notation `DUAL[` R`,` jj`]` := dual_algebra R jj 
   
This imports some basic functionality and defines the basic structure 
we'll be working with.  The ``notation`` is just for convenience, and 
we'll be using it a lot. 

Here's a couple of specializations we won't be using:


    def split_complex (R : Type*) [comm_ring R] := dual_algebra R (1)
    def dual_number (R : Type*) [comm_ring R] := dual_algebra R (0)
    def duals := dual_algebra ℝ (0)
    def splits := dual_algebra ℝ (1)

The latter two specialize over the reals, which is why R doesn't have to be 
part of the signature.   This is just plain old partial application and it
works like you'd think:

    def iduals := dual_number ℤ 
    
Now for some proofs.  Go into the namespace and set up some common variables:

    namespace dual_algebra
    variables {R:Type*} [comm_ring R] (x y jj : R) 

And prove some coercions:

    instance : has_coe R DUAL[R,jj] := ⟨λ x, ⟨x, 0⟩⟩
    instance : has_coe_t R (DUAL[R,jj]) := ⟨λ x, ⟨x, 0⟩⟩

    @[simp] lemma coe_re : (x : DUAL[R,jj]).re = x := rfl
    @[simp] lemma coe_im : (x : DUAL[R,jj]).im = 0 := rfl

    lemma coe_injective : function.injective (coe : R → DUAL[R,jj]) :=
    λ x y h, congr_arg re h
    
I think the ``instance`` is like an interface.  ``has_coe`` looks like:

    class has_coe (a : Sort u) (b : Sort v) := (coe : a → b)

and in this context it becomes:

    has_coe : Sort u_2 → Sort u_3 → Sort (max 1 (imax u_2 u_3))
   
   
The ``@[simp]`` decoration adds ``coe_re`` and ``coe_im`` to the repository 
of simplifications lean knows about, so now it'll be able to coerce
things in the base ring to things in ``DUAL[R,jj]`` as needed.

Fill out some more instances:

    @[simps {short_name:= tt}] def ε : DUAL[R,jj]:= ⟨0, 1⟩
    @[simps {short_name:= tt}] instance : has_one DUAL[R, jj] := ⟨⟨1, 0⟩⟩ 
    @[simps {short_name:= tt}] instance : has_zero DUAL[R, jj] := ⟨⟨0, 0⟩⟩ 
    @[simps {short_name:= tt}] instance : has_add DUAL[R,jj] := ⟨λ z w, ⟨z.re + w.re, z.im + w.im⟩⟩
    @[simps {short_name:= tt}] instance : has_neg DUAL[R,jj] := ⟨λ z, ⟨-z.re, -z.im⟩⟩
    @[simps {short_name:= tt}] instance : has_mul DUAL[R,jj] := ⟨λ z w, ⟨z.re * w.re + jj * z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

The ``{short_name: tt}`` attribute adds additional definitions for each field.
For example, there's now a ``has_mul_re`` with type

    has_mul_re : ∀ (jj : ?M_1) (z w : DUAL[?M_1,jj]), 
        (z * w).re = z.re * w.re + jj * z.im * w.im
        
I don't know the difference between ``@[simp]`` and ``@[simps]``.  

And now we're ready to prove that ``DUAL[R,jj]`` is a commutative ring:

    instance : comm_ring DUAL[R,jj] :=
    by refine { zero := 0, add := (+), neg := has_neg.neg, 
                one := 1, mul := (*), ..};
    { intros, ext; simp; ring }
    
We use all those instances as arguments in a constructor, and the only thing
that actually gets proved in that block is the additivity of association.

I don't know if there's an instance for that which we could have asserted or 
proven so as to avoid proving it here.

Now for algebras.  I'll admit I'm getting out of my depth here lean-wise,
but let's keep going.

I have to prove some extensionality theorems that say two ``DUAL[R,jj]`` are 
equal iff their component parts are equal:

    @[ext]
    theorem pext { z w : DUAL[R,jj]} (hre : z.re = w.re) (him : z.im = w.im) : z=w :=
    begin
      cases z with zr zi,
      cases w with wr wi,
      cc
    end

    @[ext]
    theorem rext { z w : DUAL[R,jj]} (hyp : z = w) : (z.re = w.re) ∧(z.im = w.im) := 
    begin
      cases z with zr zi,
      cases w with wr wi,
      cc
    end
    
I think that if I hadn't abstracted over ``jj`` I wouldn't need this and
could just have used the ``@[ext]`` attribute in the original definition. 

Now some more lemmas about moving from ``R`` to ``DUAL[R,jj]``.  Some of these
only got proven with trial-and-error:

    @[simp] lemma incl_one : ((1 : R) : DUAL[R,jj]) = 1 := rfl
    @[simp] lemma incl_zero : ((0 : R) : DUAL[R,jj]) = 0 := rfl

    @[simp] lemma incl_add (r s : R) : ((r + s : R) : DUAL[R,jj]) = r + s := 
    begin
      ext, refl, simp
    end

    @[simp, norm_cast] lemma coe_one : ((1 : R) : DUAL[R,jj]) = 1 := rfl

    @[simp] lemma incl_neg (r : R) : ((-r : R) : DUAL[R,jj]) = -r := 
    begin
      ext, refl, simp
    end

    @[simp] lemma incl_mul (jj r s : R) : ((r * s : R) : DUAL[R,jj]) = r * s := 
    begin
      ext, simp, simp
    end
    
Both ``simp``s are necessary in ``incl_mul``.

I'm going to guess that ``incl_add``, ``incl_neg``, and ``incl_mul`` need
the extra work because of the ``jj`` issue, as it's needed to instantiate
this homomorphism (the ``→+*``):

    def incl : R →+* DUAL[R,jj] := ⟨coe, coe_one jj, 
    incl_mul jj, incl_zero jj, incl_add jj ⟩


And finally we have that ``DUAL[R,jj]`` is an algebra over ``R``:

    instance : algebra R DUAL[R,jj]  := ring_hom.to_algebra (incl _)

We can make another homomorphism:

    def conj : DUAL[R,jj] →+* DUAL[R,jj] :=
    begin
      refine_struct { to_fun := λ z : DUAL[R,jj], 
      (⟨z.re, -z.im⟩ : DUAL[R,jj]), .. };
      { intros, ext; simp [add_comm], },
    end
    
And could have done

    instance : algebra DUAL[R,jj] DUAL[R,jj]  := ring_hom.to_algebra (conj _)

but this fails as we've already instantiated ``dual_algebra`` as an algebra.

This is about as far as I've gotten, next steps include proving ``conj`` is an 
automorphism and some fun facts about norms.

I'm not totally happy with this code, it's fragile in that it's easy to
fall into infinite loops, there's too much use of ``simp``, and 
way too much of it is magic to me, but it was fun to write and I think 
I'll continue.
