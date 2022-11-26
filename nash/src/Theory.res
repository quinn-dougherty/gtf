module Syntax = {
  type rec expr =
    | Var(variable)
    | Universe(int)
    | Pi(abstraction)
    | Lambda(abstraction)
    | App(expr, expr)
  and abstraction = {variable: variable, itsType: expr, body: expr}
  and variable =
    | String(string)
    | Gensym(string, int)
    | Dummy

  /*
(** [refresh x] generates a fresh variable name whose preferred form is [x]. *)
let refresh =
  let k = ref 0 in
    function
      | String x | Gensym (x, _) -> (incr k ; Gensym (x, !k))
      | Dummy -> (incr k ; Gensym ("_", !k))
*/
  let refresh = (x: variable): variable => {
    switch x {
    | String(x') => Gensym(x', 0)
    | Gensym(x', k) => Gensym(x', k)
    | Dummy => Gensym("_", 0)
    }
  }

  let varEq = (x: variable, y: variable): bool => {
    switch (x, y) {
    | (String(x'), String(y')) => x' == y'
    | (Gensym(x', k), Gensym(y', l)) => x' == y' && k == l
    | (Dummy, Dummy) => true
    | _ => false
    }
  }

  let rec subst = (s: list<(variable, expr)>, e: expr): expr =>
    switch e {
    | Pi(a) => Pi(substAbstraction(s, a))
    | Lambda(a) => Lambda(substAbstraction(s, a))
    | App(e1, e2) => App(subst(s, e1), subst(s, e2))
    | x => x
    }
  and substAbstraction = (s: list<(variable, expr)>, a: abstraction): abstraction => {
    let x' = refresh(a.variable)
    {
      variable: x',
      itsType: subst(s, a.itsType),
      body: subst(s->Belt.List.add((x', Var(x'))), a.body),
    }
  }
}

module TypeInference = {
  type context = list<(Syntax.variable, (Syntax.expr, option<Syntax.expr>))>
  let lookupTy = (x: Syntax.variable, ctx: context): option<Syntax.expr> =>
    ctx->Belt.List.getAssoc(x, Syntax.varEq)->Belt.Option.map(fst)
  let lookupVal = (x: Syntax.variable, ctx: context): option<Syntax.expr> =>
    ctx->Belt.List.getAssoc(x, Syntax.varEq)->Belt.Option.flatMap(snd)
  let extend = (x: Syntax.variable, ty: Syntax.expr, ~value=?, ctx: context): context =>
    ctx->Belt.List.add((x, (ty, value)))

  let rec normalize = (ctx: context, x: Syntax.expr): Syntax.expr =>
    switch x {
    | Var(x') =>
      switch lookupVal(x', ctx) {
      | None => Var(x')
      | Some(e) => normalize(ctx, e)
      }
    | App(e1, e2) => {
        let e2' = normalize(ctx, e2)
        switch normalize(ctx, e1) {
        | Lambda(a) => normalize(ctx, Syntax.subst(list{(a.variable, e2')}, a.body))
        | e1' => App(e1', e2')
        }
      }

    | Universe(k) => Universe(k)
    | Pi(a) => Pi(normalize_abstraction(ctx, a))
    | Lambda(a) => Lambda(normalize_abstraction(ctx, a))
    }
  and normalize_abstraction = (ctx: context, a: Syntax.abstraction): Syntax.abstraction => {
    let itsType = normalize(ctx, a.itsType)
    {variable: a.variable, itsType, body: normalize(extend(a.variable, itsType, ctx), a.body)}
  }

  let equal = (ctx: context, e1: Syntax.expr, e2: Syntax.expr): bool => {
    let rec equal = (e1, e2): bool => switch (e1, e2) {
      | (Syntax.Var(x1), Syntax.Var(x2)) => x1 == x2
      | (App(e11, e12), App(e21, e22)) => equal(e11, e21) && equal(e12, e22)
      | (Universe(k1), Universe(k2)) => k1 == k2
      | (Pi(a1), Pi(a2)) => equalAbstraction(a1, a2)
      | (Lambda(a1), Lambda(a2)) => equalAbstraction(a1, a2)
      | (_, _) => false
    }
    and equalAbstraction = (a1: Syntax.abstraction, a2: Syntax.abstraction): bool =>
        equal(a1.itsType, a2.itsType) && equal(a1.body, (Syntax.subst(list{(a2.variable, a1.variable->Var)}, a2.body)))
    equal(normalize(ctx, e1), normalize(ctx, e2))
  }

  let rec inferType = (ctx: context, e: Syntax.expr): option<Syntax.expr> => {
    switch e {
      | Var(x) => lookupTy(x, ctx)
      | Universe(k) => Universe(k+1) -> Some
      | Pi(a) => {
        let k1 = inferUniverse(ctx, a.itsType)
        let k2 = inferUniverse(ctx, a.body)
        switch (k1, k2) {
          | (Some(k1'), Some(k2')) => Js.Math.max_int(k1', k2') -> Universe -> Some
          | _ => None
        }
      }
      | Lambda(a) => {
        let _ = inferUniverse(ctx, a.itsType)
        let te = inferType(extend(a.variable, a.itsType, ctx), a.body)
        switch te {
          | None => None
          | Some(te') => {variable: a.variable, itsType: a.itsType, body: te'} -> Pi -> Some
        }
      }
      | App(e1, e2) => {
        open Syntax
        let a = inferPi(ctx, e1)
        let te = inferType(ctx, e2)
        switch (a, te) {
          | (Some(a'), Some(te')) => if equal(ctx, a'.itsType, te') {
                subst(list{(a'.variable, e2)}, a'.body) -> Some
            } else {
                None
            }
          | _ => None
        }
      }
    }
  }
  and let inferUniverse = (ctx: context, t: Syntax.expr): option<int> => {
    let u = inferType(ctx, t)
    switch u {
      | Some(u') => switch normalize(ctx, u') {
          | Universe(k) => k -> Some
          | _ => None
      }
      | _ => None
    }
  }
  and let inferPi = (ctx: context, e: Syntax.expr): option<Syntax.abstraction> => {
    let t = inferType(ctx, e)
    switch t {
      | Some(t') => switch normalize(ctx, t') {
          | Pi(a) => a -> Some
          | _ => None
      }
      | None => None
    }
  }
}
