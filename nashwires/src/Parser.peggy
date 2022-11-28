Expression
    = Term / "(" _ Term _ ")"
Term
    = Variable / Universe / Pi / Lambda

Pi
    = "ForAll" _ variable:Variable _ ":" _ itsType:Expression _ "." _ body:Expression {
    return {
          "constructor": "Pi",
          "variable": variable,
          "itsType": itsType,
          "body": body
    };
}

Lambda
    = "func" _ variable:Variable _ ":" _ itsType:Expression _ "." _ body:Expression {
    return {
          "constructor": "Lambda",
          "variable": variable,
          "itsType": itsType,
          "body": body
    };
}

App
    = _ e1:Expression _ e2:Expression {
    return { "constructor": "App", "left": e1, "right": e2 };
}

Universe
    = "TY" k:Natural { return { "constructor": "Universe", "index": k }; }

Variable
         = [a-z]+[a-zA-Z0-9]* {
         return { "constructor": "Var", "name": text() };
}

Natural
        = _ [0-9]+ { return parseInt(text(), 10); }

_ "whitespace"
  = [ \t\n\r]*
