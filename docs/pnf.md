If $x \notin \text{FV}(G)$ then
$$
\begin{align*}
    &(Q x) F \land G \equiv (Q x)(F \land G)\\
    &(Q x) F \lor G \equiv (Q x)(F \lor G)
\end{align*}
$$

For any formula $F$
$$
\begin{align*}
    &\lnot (\exists x) F \equiv (\forall x) \lnot F\\
    &\lnot (\forall x) F \equiv (\exists x) \lnot F
\end{align*}
$$

For any formulas $F$ and $G$
$$
\begin{align*}
    &(\forall x) F \land (\forall x) G \equiv (\forall x)(F \land G)\\
    &(\exists x) F \lor (\exists x) G \equiv (\exists x)(F \lor G)
\end{align*}
$$

If $z$ is not in $\text{FV}(F)$ nor $\text{FV}(G)$
$$
\begin{align*}
    &(\forall x) F \lor (\forall x) G \equiv (\forall x)(\forall z)(F \lor F[z/x])\\
    &(\exists x) F \land (\exists x) G \equiv (\exists x)(\exists z)(F \lor F[z/x])
\end{align*}
$$

From the above
$$
\begin{align*}
	(\exists x) F \lor (\exists y) G &\equiv
	(\exists z) F[z/x] \lor (\exists z) G[z/y] \text{ with } z \text{ not in } xyFG\\
	&\equiv (\exists z)(F[z/x] \lor G[z/y])\\
	(\forall x) F \lor (\forall y) G
	&\equiv (\forall z_0) F[z_0/x] \lor (\forall z_0) G[z_0/y] \text{ with } z_0 \text{ not in } xyFG\\
	&\equiv (\forall z_0)(\forall z_1)(F[z_0/x] \lor G[z_1/z_0][z_0/y]) \text{ with } z_1 \text{ not in } z_0xyFG\\
	&\equiv (\forall z_0)(\forall z_1)(F[z_0/x] \lor G[z_1/y]) \text{ with } z_0 \neq z_1 \text{ both not in } xyFG\\
	(\forall x) F \lor (\exists y) G
	&\equiv (\forall z_0) F[z_0/x] \lor (\exists z_0) G[z_0/y] \text{ with } z_0 \text{ not in } xyFG\\
	&\equiv (\forall z_0)(F[z_0/x] \lor (\exists z_0) G[z_0/y])\\
	&\equiv (\forall z_0)(F[z_0/x] \lor (\exists z_1) G[z_1/z_0][z_0/y]) \text{ with } z_1 \text{ not in } z_0xyFG\\
	&\equiv (\forall z_0)(F[z_0/x] \lor (\exists z_1) G[z_1/y])\\
	&\equiv (\forall z_0)(\exists z_1)(F[z_0/x] \lor G[z_1/y])\\
	(\exists x) F \lor (\forall y) G &\equiv \ldots \equiv (\exists z_0)(\forall z_1)(F \lor G) \text{ with } z_0 \neq z_1 \text{ both not in } xyFG\\
\end{align*}
$$

Analogously
$$
\begin{align*}
	(\forall x) F \land (\forall y) G &\equiv (\forall z)(F[z/x] \land G[z/x])\\
	(\exists x) F \land (\exists y) G &\equiv (\forall z_0)(\exists z_1)(F[z_0/x] \land G[z_1/x])\\
	(\forall x) F \land (\exists y) G &\equiv (\forall z_0)(\exists z_1)(F[z_0/x] \land G[z_1/x])\\
	(\exists x) F \land (\forall y) G &\equiv (\exists z_0)(\forall z_1)(F[z_0/x] \land G[z_1/x])\\
\end{align*}
$$

So for $\Box = \lor \text{ or } \land$ and completely new variables $z_0 \neq z_1$:
$$
	(Q_0 x)F \mathrel\Box (Q_1 y)G \equiv (Q_0 z_0)(Q_1 z_1)(F[z_0/x] \mathrel\Box G[z_1/y])
$$

For $z_0 \neq z_1$ new variables where $\overline{\forall} = \exists$ and $\overline{\exists} = \forall$
$$
\begin{align*}
	(Q_0 x) F \implies (Q_1 y) G 
	&\equiv \lnot (Q_0 x) F \lor (Q_1 y) G\\ 
	&\equiv (\overline{Q_0} x)(\lnot F) \lor (Q_1 y) G\\
	&\equiv (\overline{Q_0} z_0)(Q_1 z_1)(\lnot F[z_0/x] \lor G[z_1/y])\\
	&\equiv (\overline{Q_0} z_0)(Q_1 z_1)(F[z_0/x] \implies G[z_1/y])
\end{align*}
$$

For $z_0 \neq z_1$ new variables 
$$
\begin{align*}
	&(Q_0 x) F \iff (Q_1 y) G \equiv\\ 
	&(Q_0 x) F \implies (Q_1 y) G \land (Q_1 y) G \implies (Q_0 x ) F \equiv\\
	&(\overline{Q_0} z_0)(Q_1 z_1)(F \implies G) \land (\overline{Q_1} z_1)(Q_0 z_0)(G \implies F) \equiv\\
	&(\overline{Q_0} z_0)(Q_1 z_1)(F \implies G) \land (Q_0 z_0)(\overline{Q_1} z_1)(G \implies F) \equiv\\
	&(\overline{Q_0} z_0)[(Q_1 z_1)(F \implies G) \land (Q_0 z_0)(\overline{Q_1} z_1)(G \implies F)] \equiv\\
	&(\overline{Q_0} z_0)(Q_0 z_0)[(Q_1 z_1)(F \implies G) \land (\overline{Q_1} z_1)(G \implies F)] \equiv\\
	&(\overline{Q_0} z_0)(Q_0 z_0)(Q_1 z_1)[(F \implies G) \land (\overline{Q_1} z_1)(G \implies F)] \equiv\\
	&(\overline{Q_0} z_0)(Q_0 z_0)(Q_1 z_1)(\overline{Q_1} z_1)[(F \implies G) \land (G \implies F)] \equiv\\
	&(\overline{Q_0} z_0)(Q_0 z_0)(Q_1 z_1)(\overline{Q_1} z_1)[F \iff G]
\end{align*}
$$