using System;
using System.Collections.Generic;

namespace CPOR
{
    class CompoundExpression : Expression
    {
        public List<Expression> SubExpressions { get; private set; }
        public string Type
        {
            get;
            set;
        }
        public CompoundExpression()
        {
            SubExpressions = new List<Expression>();
        }
        public override string ToString()
        {
            string s = "(" + Type;
            foreach (Expression e in SubExpressions)
            {
                s += " " + e.ToString();
            }
            s += ")";
            return s;
        }

        public List<string> ToTokenList()
        {
            List<string> lTokens = new List<string>();
            lTokens.Add(Type);
            foreach (Expression e in SubExpressions)
            {
                if (e is StringExpression)
                    lTokens.Add(e.ToString());
                else
                    throw new NotImplementedException();

            }
            return lTokens;
        }
    }
}
