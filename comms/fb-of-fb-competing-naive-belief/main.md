Let `FairBot` be the player that sends an opponent to `Cooperate` (`C`) if it is provable that they cooperate with `FairBot`, and sends them to `Defect` (`D`) otherwise.

Let `FairBot_k` be the player that searches for proofs of length `<= k` that it's input cooperates with `FairBot_k`, and cooperates if it finds one, returning defect if all the proofs of length `<= k` are exhausted without one being valid.

Critch [writes](https://acritch.com/osgt-is-weird/) that "100%" of the time, mathematicians and computer scientists report believing that `FairBot_k(FairBot_k) = D`, owing to the basic vision of a stack overflow exceeding the value `k` (spoiler in the footnote[^1] for how it actually shakes out, in what is now a traditional result in open source game theory).

[^1]: it turns out that Löb's theorem implies that `FairBot` cooperates with `FairBot`, and a proof-length-aware variant of Löb's theorem implies that `FairBot_k` cooperates with `FairBot_k`.

I am one of these people who believe that `FairBot_k(FairBot_k) = D`, because I don't understand Löb, nor do I understand parametric Löb. But I was talking about this on two separate occasions with friends Ben and Stephen, both of whom made the same remark, a remark which I have not seen discussed.

# The solution set of an equation approach.

One shorter way of writing `FairBot` is this

$$FB := a \mapsto a(FB)$$

because when $a$ lands in $\{C, D\}$, $\texttt{if} a(FB) = C \texttt{then} C \texttt{else} D$ collapses to $a(FB)$.

Here, I'm being sloppy about _evaluation_ vs. _provability_. I'm taking what was originally "$a(FB)$ is provable" and replacing it with "$a$ is evaluable at $FB$", and assuming decidability so that I can reflect into `bool` for testing in an $\texttt{if}$. Then I'm actually performing the evaluation.

Stepping back, if you can write down

$$E : FB(a) = a(FB)$$

and you know that $a$ and $FB$ share a codomain (the moves of the game, in this case $\{C, D\}$), then the **solution set** of this equation $SS(E) = \text{cod} a = \text{cod} FB$. In other words, the equation is consistent at $a(FB) = C = FB(a)$ and consistent at $a(FB) = D = FB(a)$, and there may not be a principled way of choosing one particular item of $SS(E)$ in general. In other words, the proofs of the type $FB(a) = a(FB)$ are not unique.

# What the heck is the type-driven story?

I'm guessing there's some solution to this problem in [MIRI's old haskell repo](https://github.com/machine-intelligence/provability), but I haven't been able to find it reading the code yet.

I can't think of a typey way to justify $\mathbb{A} := \mathbb{A} \to \{C, D\} : Type$. It's simply nonsensical, or I'm missing something about a curry-howard correspondence with arithmoquining. In other words, agents like `FairBot` that take other agents as input and return moves are a lispy/pythonic warcrime, in terms of type-driven ideology.

# Questions

- Am I confused because of a subtlety distinguishing evaluability and provability?
- Am I confused because of some nuance about how recursion really works?
