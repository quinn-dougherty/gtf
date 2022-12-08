_Much is owed to Diffractor for Giry-pilling me at Alignable Structures, I had been struggling with type-driven expected value previously._

_Epistemic status: took a couple days off from my [master plan](https://www.lesswrong.com/posts/HbPXiB5Aiv3uHPXEh/master-plan-spec-needs-audit-logic-and-cooperative-ai) to think about John's selection theorems call to action._

We would [like](https://www.lesswrong.com/posts/G2Lne2Fi7Qra5Lbuf/selection-theorems-a-program-for-understanding-agents) a type signature of agency. [Scott Garrabrant](https://www.lesswrong.com/posts/qhsELHzAHFebRJE59/a-greater-than-b-greater-than-a) provides $(A \to O) \to A$ as a first approximation. You can choose one of two ideas here: 1. that an agent simply takes a _belief_ about how actions $A$ turn into outcomes $O$ and returns a recommended action, or 2. that an agent takes underlying configurations of reality (containing information about how actions lead to outcomes) and _tends to_ perform certain actions. Notice that $O$ happens to be for "outcome", "observation", and even "ontology", which is nice. This signature is [widely](https://ncatlab.org/nlab/show/selection+monad) discussed in the monad literature.

Scott wrote that $\to$ primarily means causal influence and secondarily means functions. I will be mostly ignoring the causal influence idea, and I think instead of thinking of the signature from an objective perspective of it being a transcription of the underlying reality, I want to think of it from a subjective perspective of it being an assistant for implementation engineers. I think we should take a swing at being incredibly straightforward about what we mean by the type signature of agency: when I say that a type $\tau$ is the type signature of agency, I mean that if we have programs that are admitted by $\tau$ then those programs are doing all the things that interest me about agents (i.e., at $\tau = (A \to B) \to A$, if we instantiate particular non-atomic propositions $A$ and $B$ that interact with the outside world in such a way that we can obtain proofs of $(A \to B) \to A$ (which we can't do in general) in some way, then those proofs are doing all the things that interest me about agents).

In my view, the first idea (involving "belief") can be called a _subjective interpretation_ of the type signature, and we shall explore some adjustments to make this story better, while the second idea (involving "base reality") can be called an _objective interpretation_ of the type signature, and we shall not explore philosophical controversies around saying that a type is "in" reality rather than in a model.

I will ultimately conclude that I am not equipped to flesh out the objective interpretation, and give a subjective interpretation such that an agent is not one selection function, but a pair of selection functions. In particular, $\mathbb{A} = Ins \mathbb{A} \oplus Epi \mathbb{A}$ (an agent is made up of an instrumental part and an epistemic part).

In the post, heading number one is an infodump about stuff I've been reading, and setup of some tooling. Heading number two is applications to agency.

### Preliminaries

- $\mapsto$ denotes _implementation of terms_ and $\to$ denotes _signature of types_. $x \mapsto e$ is an alternative to $\lambda x . e$.
- $Type$ is the type of types, which you can define via structural induction like propositional logic; the only important part for us today is $\forall A B : Type, A \to B : Type$, and I'm handwaving the equipping of preorders to arbitrary members of $Type$ very fast and loose, and I'll handwave some other stuff implying that a properly structural induction story would be really messy if I actually worked out the details.
- In [addition](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) to being a $Type$-constructor, $\to$ is also a $\mathbb{P}$-constructor (for the type of propositions $\mathbb{P}$).
- Arrows $\to$ associate to the right (see [currying](https://en.wikipedia.org/wiki/Currying)). $A \to B \to C = A \to (B \to C) \neq (A \to B) \to C$.
- We sometimes write $B^A$ instead of $A \to B$ (alluding to the arrow type's associated counting problem).
- When we say a function $\mathcal{M} : Type \to Type$ is a **monad** we mean that it comes to us equipped with a function $\eta : X \to \mathcal{M} X$ (called a _return_) and a function $\mu : \mathcal{M} \mathcal{M} X \to \mathcal{M} X$ (called a _flatten_) which agree to some [laws](<https://en.wikipedia.org/wiki/Monad_(functional_programming)#Definition>).
  - **Example**: let $\mathcal{M} := list$ setting $\eta$ to the construction of a singleton and $\mu$ to the removal of nesting information.
  - **Exercise**: fixing an $A : Type$, one of $\mathcal{M} := B \mapsto B^A$ or $\mathcal{M} := B \mapsto A^B$ forms a monad. Pick one and set its $\eta$ and $\mu$ (Solution[^0]).

[^0]: [not super useful without an interactive session, nevertheless](https://github.com/quinn-dougherty/gtf/blob/ee4f11c9f2044767c63506632ae4db7d69185fbc/game-theory/theories/SelectionContinuation.v).

# Selection and continuation

The agent type is widely discussed in the monad literature.

Fixing an outcome type $S$, $\mathcal{J}_S := X \mapsto (X \to S) \to X : Type \to Type$ is called the _selection monad_, and its friend $\mathcal{K}_S := X \mapsto (X \to S) \to S : Type \to Type$ is called the _continuation monad_.

## Remark: quantifiers are continuations

### Preliminaries

- $\mathbb{B} := \{true, false\}$, or the type of two nullary construcors.
- $\mathbb{R}$ is the complete ordered field.

The story of $\mathbb{B}$-valued or $\mathbb{B}$-interpreted logics goes like this. For any $X : Type$,

$$(\forall x : X) (\exists x : X) : \mathcal{K}_{\mathbb{B}} X$$

In other words, a quantifier takes a predicate (typed $X \to \mathbb{B}$) and returns a valuation of the predicate under different conditions. $\forall x : X$ is the element of $\mathcal{K}_{\mathbb{B}} X$ that says "the predicate is true all over $X$", $\forall x : X, k x$ (or we may write it point-free as $\forall k$) is $true$ if and only if $k x$ is always $true$ regardless of $x$. $\exists x : X$ is the element of $K_{\mathbb{B}} X$ that says "the predicate is true at least once over $X$", the point-free $\exists k$ is $true$ if and only if you can provide at least one $x$ such that $k x$ is $true$.

The literature likes to call continuations _generalized quantifiers_, where your "truth values" can take on arbitrary type. The story of quantifiers can be updated to $\mathbb{P}$ for a richer type of propositions such that not everything is decidable.

### Exercises:

- Think of distinguished primitives in reinforcement learning theory; is there either a selection or a continuation story one of them? (Solution[^1]).
- Name a distinguished primitives from calculus or analysis; is there a selection or continuation story of it? (Solution[^2]).

[^1]: $\forall X : Type, \arg\max : \mathcal{J}_{\mathbb{R}} X$
[^2]: $\forall X : Type, \max : \mathcal{K}_{\mathbb{R}} X$

## Remark: distributions are a special case of generalized quantifiers

### Preliminaries

- Recall that for each $y \in B$, you can construct a **constant** function $\tilde{y} := x \mapsto y : A \to B$ by throwing out the $x$.
- A $\leq_X : X \to X \to \mathbb{P}$ is a reflexive and transitive relation.
- Recall that an $\alpha : A \to B$ is **monotonic** when, having a $\leq_A$ and a $\leq_B$, $\forall x y : A, x \leq_A y \to \alpha x \leq_B \alpha y$.
- Let $\leq_{B^A} := \alpha \mapsto \beta \mapsto \forall x : A, \alpha x \leq \beta x : B^A \to B^A \to \mathbb{P}$.
- A map $\alpha : B^A$, when $A$ and $B$ are drawn from some underlying field $\mathbb{F}$, is **linear** whenever $\forall k l : \mathbb{F}, \forall x y : A, \alpha (k x + l y) = k \alpha x + l \alpha y$.

### Consume a valuation and produce an expectation

A particular way of strengthening or filtering $\mathcal{K}_{\mathbb{R}}$ (quantifiers generalized to valuations in $\mathbb{R}$) is to require linearity, monotonicity, and the sending of constant functions to a neutral scalar. For arbitrary types $A, B$ and for types $C$ equipped with some multiplicative structure involving a neutral, we will write $B^A \overset{\leq}{\multimap} C$ to describe the functions $B^A \to C$ but only keeping the ones that are monotonic, linear, and that send constants in $B^A$ to the multiplicative neutral in $C$ (conventionally, $\multimap$ pronounced "lollipop" or "lolli" denotes linearity). Letting $\mathbb{R}$ play the roles of $B$ and $C$, define $$\Delta := X \mapsto \mathbb{R}^X \overset{\leq}{\multimap} \mathbb{R} : Type \to Type$$

In other words, a distribution is just a continuation term that knows how to turn a valuation (an $X \to \mathbb{R}$, i.e. a random variable) into an expectation (where the expectation abides linearity, monotonicity, and the sending of constants to $1$).

$$\forall X : Type, \forall \mu, \mathbb{E}_{\mu} := \alpha \mapsto \int_X \alpha d\mu : \Delta X$$

where I'm being lazy about the measure theory needed to actually compute terms, however, we see that measure theory doesn't really emerge at the type level.

I'm thinking of distributions as a subset of these $\mathbb{R}$-valued quantifiers because I want to eventually think about utilities, and I'm still pretty sure the utility codomain is going to be $\mathbb{R}$ all the time.

### $\Delta$ forms a monad

The settings of $\eta$ and $\mu$ along with the lawfulness proofs are in [this `coq` file](https://github.com/quinn-dougherty/gtf/blob/a5e22b933922e57d844ac653d4b48ce043aa74f3/game-theory/theories/Giry.v#L53), written a few weeks ago before I knew anything about the selection and continuation literature. (This is not surprising, as we knew that $\mathcal{K}_{\mathbb{R}}$ forms a monad, and the substitution of the second $\to$ for $\overset{\leq}{\multimap}$ only deletes maps and doesn't add any potential violators).

## Remark: convert selections into continuations/quantifiers

$$\forall A B : Type, \bar{.} := \epsilon \mapsto k \mapsto k (\epsilon k) : \mathcal{J}_B A \to \mathcal{K}_B A$$

In other words, if $\epsilon$ is a selection then $\bar{\epsilon}$ is a continuation.

### Attainability

Presume a $A B : Type$. Suppose I have a $k : \mathcal{K}_B A$. $k$ is called **attainable** when it's preimage under $\bar{.}$ is nonempty. In other words, $k$ is attainable if and only if $\exists \epsilon : \mathcal{J}_B A, \forall \alpha : B^A, k \alpha = \alpha (\epsilon \alpha)$. In that case, we may say "$\epsilon$ attains $k$".

Notice that from the existence half of the functionality predicate, we get a free existence proof of a continuation/quantifier for every selection. To believe that some continuations are unattainable is to believe that $\bar{.}$ is not surjective.

### Exercise

- Recall the solutions to previous exercises 1 and 2. What is the attainability relationship between them, if any?[^3]

[^3]: $\arg\max$ attains $\max$, or $\overline{\arg\max} = \max$.

## Wrapping the codomain

Fix a $\mathcal{F} : Type \to Type$ and a $S : Type$. Define

$$\mathcal{J}^{\mathcal{F}}_S := X \mapsto (X \to S) \to \mathcal{F} X : Type \to Type$$
$$\mathcal{K}^{\mathcal{F}}_S := X \mapsto (X \to S) \to \mathcal{F} S : Type \to Type$$

### Example: powerset

Denote $\mathcal{P}$ as the function that confiscates a type and rewards the powerset of that type. In other words, $\mathcal{P} := X \mapsto X \to \mathbb{B} : Type \to Type$ (where an $\alpha : \mathcal{P} X$ is interpreted $x "\in" \alpha$ if and only if $\alpha x = true$).

We call the items of $\mathcal{J}^{\mathcal{P}}_S$ **multi-valued selections** and items of $\mathcal{K}^{\mathcal{P}}_S$ **multi-valued quantifiers**.

### Exercise (harder than previous)

- can you re-obtain monadicity for multi-valued selection?
- can you re-obtain monadicity for multi-valued continuation?
- write down multi-valued attainment[^4]

[^4]: Presume some $X S : Type$ and some $K : \mathcal{K}^{\mathcal{P}}_S X$. $K$ is attainable if and only if $\exists \varepsilon : \mathcal{J}^{\mathcal{P}}_S X, \forall \alpha : S^X, \forall x : X, (\varepsilon \alpha) x = true \to (K \alpha) x = true$. For multi-valued variants of $\max$ and $\arg\max$, we can check that the solution to exercise 2 transfers over to this setting.

## Wrapping the codomain of the domain

We may additionally like to use maps $\mathcal{F} : Type \to Type$ to goof off with transforming the codomain of the input map.

$$\mathcal{J}^{(\mathcal{F})}_S := X \mapsto (X \to \mathcal{F} S) \to X : Type \to Type$$
$$\mathcal{K}^{(\mathcal{F})}_S := X \mapsto (X \to \mathcal{F} S) \to S : Type \to Type$$

### Exercise

- again, can you re-obtain monadicity for $\mathcal{J}^{(\mathcal{P})}_S$? For $\mathcal{K}^{(\mathcal{P})}_S$?

## Wrapping the whole domain

Having maps $\mathcal{F} : Type \to Type$, and since $X \to S : Type$, we also might enjoy transforming the whole input map type.

$$\mathcal{J}^{[\mathcal{F}]}_S := X \mapsto \mathcal{F} (X \to S) \to X : Type \to Type$$
$$\mathcal{K}^{[\mathcal{F}]}_S := X \mapsto \mathcal{F} (X \to S) \to S : Type \to Type$$

# Modifying the agent signature

Recall the agent interpretation of selection. We fix an outcome type $O$ and an action type $A$ and we reason about $\mathcal{J}_O A = (A \to O) \to A$. Recall that there are two cases: a **subjective** case in which items $A \to O$ are _beliefs_, and an **objective** case in which items $A \to O$ are _actual configurations of reality_. In the subjective case, an agent turns a model of reality into a recommended action (the term hardcodes its notion of utility or whatever). In the objective case, the world has configurations, and an agent can be trusted to tend toward the actual configuration over time, using it to (again relying on hardcoded utility data) select actions.

## Investigation: continuation is to $\Delta$ as selection is to what?

We obtained $\Delta$ by replacing the rightmost $\to$ in the definition of $\mathcal{K}_{\mathbb{R}} X$ with my custom $\overset{\leq}{\multimap}$. Let's goof around with performing the same replacement in $\mathcal{J}_{\mathbb{R}} X$.

$$\Delta_* := X \mapsto \mathbb{R}^X \overset{\leq}{\multimap} X : \textit{"Type"} \to Type$$

Recall that $\overset{\leq}{\multimap}$ implies that it's codomain supports linearity, monotonicity, and multiplicative neutrality, so we know that the domain of $\Delta_*$ isn't "really" just $Type$ (hence the scare quotes), whereas the domain of $\Delta$ was truly the unconstrained type $Type$. So it may be difficult now to be sure of the preservation of monadicity.

### Preliminaries

- A monoidal preorder is a preorder with a monoid attached. If you start with $(P, \leq)$ such that $\leq$ is reflexive and transitive, and you find an associative $\otimes : P \to P \to P$ that has a distinguished neutral element $\epsilon$, and you know $\forall a b c d : P, a \leq c \to b \leq d \to a \otimes b \leq c \otimes d$, then you have the monoidal preorder $(P, \leq, \epsilon, \otimes)$.
  - From any set $A$ you can construct a monoidal preorder $(\mathcal{P} A, \subseteq, A, \cap)$ where $\subseteq$ and $\cap$ are from set theory. Validate this, if you like.

### Rambling about $\Delta_*$

How do we interpret this? In the agent case, actions are playing the role of $X$, which immediately suggests that we'll only have the class of continuous action spaces, so we can try $\mathbb{R}$. But $\Delta_* \mathbb{R} = \mathbb{R}^{\mathbb{R}} \overset{\leq}{\multimap} \mathbb{R} = \Delta \mathbb{R}$, which feels maybe problematic or vacuous. Possibly problematic, because I don't know how the theory of random variables adjusts to the bare real line (as opposed to a collection of subsets). Possibly vacuous, because I don't know any particular terms typed $\mathbb{R} \to \mathbb{R}$ (other than $x \mapsto x$ or ones with fairly strong conditions like increasingness) that I would expect to correspond with some foggy coherence notion for valuations in the back of my mind. Moreover, what should we think of collapsing the very distinction between selection and continuation, by setting $S = X$? $(X \to X) \to X$ isn't provable in the logic interpretation (unless I'm missing some coinductive black magic resolving loops), which is a hint that we're barking up the wrong tree. My gut isn't telling me $\Delta_* [0,1]$ would be any better.

We could of course support the $\overset{\leq}{\multimap}$ requirements on the codomain by putting a monoidal preorder on $\mathbb{B}^X$ (namely setting $P := \mathbb{B}^X$, $\leq := \subseteq$, $\epsilon := X$, and $\otimes := \cap$), which wouldn't work for entirely arbitrary $X : Type$ but would work if you could interpret the scaling of a subset (like $X$ is a single suit out of a deck of cards, the valuation $\nu$ of a subset is the total number of pips across all the cards in the subset, and scalar $k$ hits it by doing some operation on that valuation, like $k := p \mapsto \lfloor |k \nu p| \rfloor$). Fix an $X$ that you can interpret in this way. Then, try $\Delta_* \mathbb{B}^X = ((X \to \mathbb{B}) \to \mathbb{R}) \overset{\leq}{\multimap} X \to \mathbb{B}$. In other words, if I have an $X$-generated multi-valued "selection distribution" $E : \Delta_* \mathbb{B}^X$, then for every valuation of a subset $\nu : \mathbb{B}^X \to \mathbb{R}$, $E \nu$ is a kind of expected subset, or it's something the agent can proactively search for like $\arg\min$ or $\arg\max$. Perhaps you could even interpret/implement it like "if $\nu$ is my complete account of what a subset is worth to me, then $E$ fixes an amount of optimization power I'm going to throw at steering the future into particular subsets over others, and $E \nu$ denotes the sort of place I would end up if I applied that much optimization to my values (insofar as landing at an actual optima implies that possibly unbounded optimization power was deployed)".

### Exercise

- Check that monotonicity, linearity, and the sending of constants to $1$ (in this case $X$ because it's the monoidal neutral) works with something like my deck-of-cards choice of $X$.

### What about $\Delta^{\mathcal{C}}_* X$ for metric spaces $X$?

Loosening up the pedantry a little, because the actual type-driven story would get too hairy, let's by fiat admit $\mathcal{C}[0,1] : Type$, so we can take the subset of $\mathbb{R}^{[0,1]}$ that just has continuous functions in it. You shall indulge me if I utilize $\mathcal{C} : Type \to Type$ without properly saying that the domain is just the types interpretable as or isomorphic to uninterrupted intervals, whatever.

$$\Delta^{\mathcal{C}}_* = X \mapsto (X \to \mathbb{R}) \overset{\leq}{\multimap} \mathcal{C} X = X \mapsto (X \to \mathbb{R}) \overset{\leq}{\multimap} X \overset{\mathcal{C}}{\to} \mathbb{R}$$

A modus ponens with a little decoration with conditions like the linearity/monotonicity/sending constants to $1$ and continuity. What does it mean?

It could mean the environment actually giving the agent a reward for taking action $X$, though it's a simpler story than the one in standard reinforcement learning theory, especially e.g. POMDPs.

### Lastly, $\Delta_* \circ \mathcal{C}$

The idea of rigging "scalar multiplication" to my deck of cards semantics was uncomfortable. The following, however, has a perfectly natural notion of linearity (alongside order and the idea of a $1$).

$$\Delta_* \circ \mathcal{C} = X \mapsto (\mathcal{C} X \to \mathbb{R}) \overset{\leq}{\multimap} \mathcal{C} X = X \mapsto ((X \overset{\mathcal{C}}{\to} \mathbb{R}) \to \mathbb{R}) \overset{\leq}{\multimap} X \overset{\mathcal{C}}{\to} \mathbb{R}$$

Selections over continuous functions (taking valuations of continuous functions as inputs and returning continuous functions as output) sounds like a kind of learning over "metavalues", when the continuous functions are interpreted as utilities, then the $\arg\max : (\Delta_* \circ \mathcal{C}) X$ knows how to take the utility of a utility function (which is metautility) and choose the one that maximizes metautility.

This of course restricts that the action type be equipped with a metric.

### Conjecture: attainability survives the transportation to the custom $\overset{\leq}{\multimap}$

$\forall X : \textit{"Type"}, \bar{.} : \Delta_* X \to \Delta X$ should be provable. Indeed, it's just a domain restriction on the original $\bar{.}$, so this conjecture is in the bag.

## Investigation: $\mathcal{J}^{[\Delta]}_O$

$$\mathcal{J}^{[\Delta]}_S := X \mapsto \Delta (X \to O) \to X : Type \to Type$$

This isn't quite the subjective approach I'm looking for. Mapping from uncertainty over valuations to actions seems kinda from the perspective of social choice theory, where the difference in opinion across the population is captured by not being able to know a precise point estimate of a valuation, having to turn a distribution over valuations of actions into an action.

## Investigation: $\mathcal{J}^{(\Delta)}_S$

$$\mathcal{J}^{(\Delta)}_S := X \mapsto (X \to \Delta S) \to X : Type \to Type$$

This looks to me the most like "the agent turns models/beliefs into actions".

Let's unfold $\Delta$.

$$\mathcal{J}^{(\Delta)}_S = X \mapsto (X \to (\mathbb{R}^X \overset{\leq}{\multimap} \mathbb{R})) \to X : Type \to Type$$

The general pattern of "terms such that the input is $X$ into quantifiers and the output is $X$" might mean that terms are hardcoded predicates which can select values of $X$ to get a desired result _depending_ on whichever quantifier shows up. We will not work with the unfolded version in what follows.

## Rescue attempt: the objective interpretation

In the objective interpretation of the type signature of agency, an agent is a term that turns a configuration reality could be in (specifically the information about how actions lead to outcomes) into an action.

In my rescue operation, objectivity is not pure: we will see that I've installed a subjectivity (i.e. learning) layer as an implementation detail. Think of it like the difference between a lemma and a theorem; at the lemma level, there's subjectivity, while if the theorem level doesn't open up black boxes it may not notice subjectivity. Put another way, the challenge of the rescue operation is to tell a compellingly full story (which ought to oblige the term to empiricism under uncertainty) without resorting to $\Delta$.

The "lemma" will be a term $\phi : \mathcal{J}_{\mathbb{R}} O^A$. Its inputs $O^A \to \mathbb{R}$ are loss functions which come equipped with real-world data hardcoded into them. These loss functions make sense of the gap between a map and a territory, here focusing on action-output relations, i.e. they take a notion of how actions turn into outcomes and they score how accurate it is. Then for such a loss function $l : O^A \to \mathbb{R}$, $\phi l : A \to O$. (And if you want the function that constructs $l$s, you need ontology to describe that function's domain). Since this is the objective point of view, we interpret $\phi l$'s codomain as the literal outcomes in the world, indeed $\phi l$ _is_ the gears by which perturbations from agents effect things. (Warning: [here be monsters](https://www.lesswrong.com/posts/gEKHX8WKrXGM4roRC/saving-time)) if we say that in order to implement an agent you need to provide a $\phi$, and $\phi l$ describes the literal gears of the world and isn't a conditional forecast (like "our best guess at time $t$ is that action $x$ will transition the world into state $(\phi_t l) x$"), then I don't see how an agent is remotely computational.

Equipped like so, with any proof $\epsilon : \mathcal{J}_O A$ hardcoded by some humans or learned by some ML model, and some $l : O^A \to \mathbb{R}$ provided by a stakeholder/principal, $(\epsilon \circ \phi) l$ is the action the proof would like to take. But since $\phi$ is a blackbox, $(\epsilon \circ \phi) l$ is as good as an axiom, i.e., the blackboxness propagates out and it _can't_ be actually written at the low level. A configuration of the world $((\phi l) \circ \epsilon \circ \phi) l$ has a similar problem.

It's plausible to me that infrabayesian physicalism or factored sets provide a way forward, but I'm not going to grok either of those today. (The first time I read "Saving Time" just as now, I was confused about "the future effects the past" because of the determinism/nondeterminism question, i.e. I get that forecasts of or distributions over the future effect the past, but I don't get how the actual future effects the past).

I'm marking this rescue operation as a _failure_, owing to the restriction against invoking $\Delta$.

## Rescue: the subjective interpretation

### Preliminaries

- We will use **pair types**, of one constructor (namely $(\cdot, \cdot) := a \mapsto b \mapsto (a,b) : A \to B \to A \times B$) and two destructors (namely $\pi_1 := (a, b) \mapsto a : A \times B \to A$ and $\pi_2 := (a, b) \mapsto b : A \times B \to B$), and we assume associativity of $n$-ary or nested products.

### A subjective agent is a tuple with a protocol

In the subjective interpretation of the type signature of agency, an agent is a term that knows how to turn a _belief_ about how actions turn into outcomes into an action. Since beliefs are emphasized, and beliefs are uncertain, we will allow ourselves liberal use of the $\Delta$ operator. The following approach is based on the failed rescue of the objective interpretation.

Fix a type $A$ of actions and a type $O$ of outcomes. We consider proofs $\psi : \mathbb{N} \to \mathcal{J}_{\mathbb{R}} (A \to \Delta O)$ where items $f : A \to \Delta O$ are _conditional forecasts_ that accept an action $x$ and report, with uncertainty, a belief about what will happen if it does $x$. As the domain of $\phi$ above, for any $t : \mathbb{N}$ the domain of $\psi t$ is _loss functions_, each of which considers a conditional forecast $f$ and scores it for calibration, accuracy, whatever. We write $\psi_t$ instead of $\psi t$.

A stakeholder or principal encodes observations at time $t$ of the world by hardcoding data into their choice of loss function by using the function $L : \mathbb{N} \to (A \to \Delta O) \to \mathbb{R}$, writing $l = L_t$ instead of $L t$.

Then implement the uncertain selection $\epsilon : \mathcal{J}^{(\Delta)}_O A$. Notice that it's domain is conditional forecasts.

Then an agent is none other than $\mathbb{A} := (\epsilon, \psi) : \mathcal{J}^{(\Delta)}_O A \times (\mathbb{N} \to \mathcal{J}_{\mathbb{R}} (A \to \Delta O))$ with sensors and actuators, which interacts with the world via a protocol $\pi$ which runs as follows

1. At time $t+1$, a stakeholder or principal sets $l = L_t$ and hands it to $\mathbb{A}$.
2. $\psi_{t+1} l$ is a conditional forecast that turns actions into uncertainty in $O$. $(\epsilon \circ \psi_{t+1}) l$ is the action taken by $\mathbb{A}$ at time $t+1$.
3. Observe world $\omega : O$ and score the term $\Omega = ((\psi_{t+1} l) \circ \epsilon \circ \psi_{t+1}) l : \Delta O$ against it, using the score to power some search process that informs $\psi_{t+2}$.
4. Increment $t$ and repeat.

In other words, the agent calculates an action because it can turn loss functions which score conditional forecasts into a handpicked conditional forecast, and it can also turn conditional forecasts into handpicked actions. $\psi$ hardcodes the procedure for doing bayesian updates, i.e. it has opinions about some beliefs being better than others. $\epsilon$ hardcodes (and hides) a utility function, i.e. it has opinions about some outcomes being better than others. Echoing a complex number, which is a real part and an imaginary part, we can view an agent $\mathbb{A}$ as an instrumental part and an epistemic part. While the complex numbers are equipped with some notion of "$+$" such that $z := \pi_1 z + \pi_2 z$ (real part plus imaginary part), I can make up a notion of "$\oplus$" such that

$$\forall L : \mathbb{N} \to (A \to \Delta O) \to \mathbb{R}, \forall t : \mathbb{N}, \mathbb{A}_t := ((\pi_2 \mathbb{A}) (t + 1) (L t)) \circ (\pi_1 \mathbb{A}) \circ (\pi_2 \mathbb{A}) (t + 1) (L t) \oplus (\pi_1 \mathbb{A}) \circ (\pi_2 \mathbb{A} (t + 1) (L t))$$

(epistemic part "plus" instrumental part).

I played fast and loose with the **mutability** and implicit **differentiability** of $\psi$. I think this is appropriate: any intuition about agents is that their beliefs change over time, even if corrigibility remains an open problem (in other words, epistemic part ought to be mutable even if the instrumental part (where the utility function is) is not).

The abstract type signature of $\pi$ is $\mathbb{N} \to O$, where here when we say a codomain is outcomes we mean that it's the literal world, not an implementational model of it, hence the signature being "abstract".

### Selection product?

In the literature there's a function $\mathcal{J}^{\times}_S := J_1 \mapsto J_2 \mapsto \mathcal{J}^{\times}_S J_1 J_2 : \mathcal{J}_S A \to \mathcal{J}_S B \to \mathcal{J}_S (A \times B)$. It's only defined between selections that share an inner target $S$, though, so it doesn't apply to $\mathbb{A}$. Still, there might be some cleverness I haven't considered.

# Conclusion

We need more candidates for the type signature of agency. An obvious way to explore is to take the first candidate someone wrote down, make an incision, and poke its guts with various functions $\mathcal{F} : Type \to Type$.

A more complete story of agency, together with a protocol describing interactions with the world, is not a single selection but a pair of selections. The pair can be understood as an epistemic part and an instrumental part.

I'm aware that I at least partially took some steps toward reinventing the reinforcement learning theory wheel when I gave the protocol $\pi$, an alternative approach to this post would be to start with RL theory and see what notions of selection function are hanging around.

If we hammer out the dents in $\Delta_*$ we get a really pretty notion of "turning agency into probability" (in the form of the function $\bar{.}$ on a restricted domain), and plausibly also a characterization of the unreliability or impossibility of turning probability into agency (via the insurjectivity of $\bar{.}$).

What _about_ interp? I think something like the [searching for search](https://www.lesswrong.com/posts/FDjTgDcGPc7B98AES/searching-for-search-4) could, if we're not totally and completely wrong about the pillars of the agency type signature direction, show us a _ton_ about how ML naturally implements terms/proofs of things like $\mathcal{J}_S X$. A dope UX would be something like [tactical programming](https://pjreddie.com/coq-tactics/) not for creating terms/proofs, but for parsing out / identifying them in a big pile/soup of linear algebra. A fantasy world I'd like to live in is one where a prosaic/interp shop ships `neural-hoogle` or `transformer-hoogle`, a search engine that accepts type signatures and finds configurations of matrices and weights which, if you squint, count as proofs/terms of those types. To be abundantly clear, you can think of the following proof of $J_{\texttt{float}} A$ as the dumbest possible search

```python
def argmax(f: Callable[[A], float]) -> A:
  ret = None
  curr_y = - 2 ** 100
  for x in A:
    y = f(x)
    if y > curr_y:
      curr_y = y
      ret = x
  return ret
```

Insofar as the type `A` is enumerable. The hypothesis advanced by this post is that arbitrarily not-dumb search is constrained by the same type information as dumb search. Search is _literally_ a significant class of proofs of selection.

The objective interpretation of the project of giving a type signature for agents seems a little borked right now, but that could change with increased understanding of factored sets or maybe infrabayesian physicalism.

Selections and continuations play a huge role in compositional game theory, which I'm starting to think provides a mean embedded agency story, though I haven't grokked it quite at the level of writing a post about it just yet.

# References

- [selection on nlab](https://ncatlab.org/nlab/show/selection+monad) (recursing into citations)
- [several Jules Hedges publications](https://julesh.com/publications/)
- [selections in software engineering](https://youtu.be/riW9gRDNrVw)
