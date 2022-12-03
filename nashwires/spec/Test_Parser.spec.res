open RescriptMocha
open Mocha
open Theory.Syntax

/*
    This helper tests from top level input string all the way to expression, skipping the node object IR.
*/
let testParse = (description: string, nashString: string, output: expr) => {
  let dummyString = "main"
  description->it(() => {
    switch nashString->Parser.parse(dummyString) {
    | Ok(p) => Assert.deep_equal(p->Parser.makeExpression, output->Some)
    | Error(e) => Assert.deep_equal(e, Parser.SyntaxError("unpredictable")) // TODO: actually use error.
    }
  })
}

let enclose = (x: string): string => "(" ++ x ++ ")"

"parses without recursion"->describe(() => {
  "U1"->testParse("TY1", Universe(1))
  "U9140"->testParse("TY9140", Universe(9140))
  // TODO: expected error handling.

  let x = "x"
  let x1 = "x1"
  let fooski = "fooski"
  let barski12345 = "barski12345"
  let names = [x, x1, fooski, barski12345]
  for i in 0 to names->Js.Array.length - 1 {
    let name = names[i]
    name->testParse(name, name->String->Var)
  }
  // TODO: expected error handling.

  "ForAll with just a var as body"->testParse(
    "ForAll x1 : TY2, x1",
    {variable: "x1"->String, itsType: 2->Universe, body: "x1"->String->Var}->Pi,
  )
  "ForAll with just a universe as body"->testParse(
    "ForAll fooski: TY2 , TY1",
    {variable: "fooski"->String, itsType: 2->Universe, body: 1->Universe}->Pi,
  )

  "func with just a var as body"->testParse(
    "Func x: TY0 . x",
    {variable: "x"->String, itsType: 0->Universe, body: "x"->String->Var}->Lambda,
  )

  "App of two vars"->testParse("$ x1 y", App("x1"->String->Var, "y"->String->Var))
})

// "parses with recursion"->describe(() => {
//  "ForAll with a ForAll as input's type and an App in the body"->testParse(
//    "ForAll x : (ForAll y: TY0, y) , $ x y",
//    {
//      variable: "x"->String,
//      itsType: {variable: "y"->String, itsType: 0->Universe, body: "y"->String->Var}->Pi,
//      body: App("x"->String->Var, "y"->String->Var),
//    }->Pi,
//  )
//  "ForAll with an App as input's type and an App in the body"->testParse(
//    "ForAll x: ($ y z), $ x z",
//    {
//      variable: "x"->String,
//      itsType: App("y"->String->Var, "z"->String->Var),
//      body: App("x"->String->Var, "z"->String->Var),
//    }->Pi,
//  )
// })
