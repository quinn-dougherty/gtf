module Stx = Theory.Syntax

type constructorFlag = {"constructor": string}

@module("./Parser.js")
external parse__: (string, {"grammarSource": string}) => constructorFlag = "parse"

type parseError = SyntaxError(string)

type parseResult = result<constructorFlag, parseError>

let parse = (expr: string, source: string): parseResult =>
  try {
    let theParse = expr->parse__({"grammarSource": source})
    theParse->Ok
  } catch {
  | Js.Exn.Error(obj) => obj->Js.Exn.message->Belt.Option.getExn->SyntaxError->Error
  }

type nodeVar = {...constructorFlag, "name": string}
type nodeUniverse = {...constructorFlag, "index": int}
type nodeAbs = {
  ...constructorFlag,
  "variable": nodeVar,
  "itsType": constructorFlag,
  "body": constructorFlag,
}
type nodeApp = {...constructorFlag, "left": constructorFlag, "right": constructorFlag}

external castNodeVar: constructorFlag => nodeVar = "%identity"
external castNodeUniverse: constructorFlag => nodeUniverse = "%identity"
external castNodeAbs: constructorFlag => nodeAbs = "%identity"
external castNodeApp: constructorFlag => nodeApp = "%identity"

let rec makeExpression = (root: constructorFlag): option<Stx.expr> => {
  switch root["constructor"] {
  | "Var" => root->castNodeVar->makeVariable->Belt.Option.map(s => Stx.Var(s))
  | "Universe" => root->castNodeUniverse->(x => x["index"])->Universe->Some
  | "Pi" => root->castNodeAbs->makeAbstraction->Belt.Option.map(a => Stx.Pi(a))
  | "Lambda" => root->castNodeAbs->makeAbstraction->Belt.Option.map(a => Stx.Lambda(a))
  | "App" => {
      let node = root->castNodeApp
      let e1 = node["left"]
      let e2 = node["right"]
      switch (e1->makeExpression, e2->makeExpression) {
      | (Some(e1'), Some(e2')) => App(e1', e2')->Some
      | _ => None
      }
    }

  | _ => None
  }
}
and makeVariable = (var: nodeVar): option<Stx.variable> => {
  var["name"]->String->Some
}
and makeAbstraction = (a: nodeAbs): option<Stx.abstraction> => {
  let t = a["itsType"]->makeExpression
  let e = a["body"]->makeExpression
  let x = a["variable"]->makeVariable
  switch (x, t, e) {
  | (Some(x'), Some(t'), Some(e')) => {variable: x', itsType: t', body: e'}->Some
  | _ => None
  }
}
