using CPORLib.LogicalUtilities;
using CPORLib.PlanningModel;
using System;
using System.Collections.Generic;


namespace CPORLib.FFCS
{
    public class InputConverter
    {
        public bool Process(Domain d, Problem p)
        {
            SetTypes(d);
            SetConstants(d);
            SetPredicates(d);
            SetActions(d);

            SetGoal(p);
            SetStartState(p);

            return true;
        }

        private void SetActions(Domain d)
        {
            List<PlOperator> lOperators = new List<PlOperator>();
            foreach (PlanningAction a in d.Actions)
                lOperators.Add(Convert(a));
            for(int i = 0; i < lOperators.Count - 1; i++)
            {
                lOperators[i].next = lOperators[i + 1];
            }
            FF.Parsing.gloaded_ops = lOperators[0];
        }

        private PlOperator Convert(PlanningAction a)
        {
            PlOperator op = new PlOperator(a.Name);
            if (a is ParametrizedAction pa)
            {
                List<TypedList> lParams = new List<TypedList>();
                foreach(Parameter p in pa.Parameters)
                {
                    TypedList tl = new TypedList(p.Name, p.Type);
                    lParams.Add(tl);
                }
                if (pa.Parameters.Count > 0)
                {
                    for (int i = 0; i < lParams.Count - 1; i++)
                        lParams[i].next = lParams[i + 1];
                    op.parse_params = lParams[0];
                }
                else
                    op.parse_params = null;
                op.number_of_real_params = pa.Parameters.Count;
            }
            op.preconds = Convert(a.Preconditions);
            op.effects = Convert(a.Effects);
            return op;
        }

        private void SetStartState(Problem p)
        {
            CompoundFormula cf = new CompoundFormula("and");
            foreach (Predicate pInit in p.Known)
            {
                if (!pInit.Negation)
                    cf.AddOperand(pInit);
            }
            FF.Parsing.gorig_initial_facts = Convert(cf);
        }

        private void SetGoal(Problem p)
        {
            FF.Parsing.gorig_goal_facts = Convert(p.Goal);
        }

        private void SetPredicates(Domain d)
        {
            //predicates: gparse_predicates

            List<TypedListList> lPredicates = new List<TypedListList>();
            foreach(Predicate p in d.Predicates)
            {
                TypedListList tll = new TypedListList();
                tll.predicate = p.Name;
                if (p is ParametrizedPredicate pa)
                {
                    List<TypedList> lArgs = new List<TypedList>();
                    foreach(Parameter a in pa.Parameters)
                    {
                        TypedList tl = new TypedList(a.Name, a.Type);
                        lArgs.Add(tl);
                    }
                    if(lArgs.Count > 0)
                    {
                        for(int i = 0; i < lArgs.Count - 1; i++)
                        {
                            lArgs[i].next = lArgs[i + 1];

                        }
                        tll.args = lArgs[0];
                    }
                }
                lPredicates.Add(tll);
            }
            if(lPredicates.Count > 0)
            {
                for(int i = 0; i < lPredicates.Count - 1; i++)
                {
                    lPredicates[i].next = lPredicates[i + 1];
                }
                FF.Parsing.gparse_predicates = lPredicates[0];
            }

        }

        private PlNode Convert(Formula f)
        {
            PlNode n = null;
            if (f == null)
                return null;
            if (f is CompoundFormula cf)
            {
                List<PlNode> lSons = new List<PlNode>();
                foreach (Formula fSub in cf.Operands)
                {
                    lSons.Add(Convert(fSub));
                }
                if (cf.Operator == "and")
                {
                    n = new PlNode(Connective.AND);
                }
                else if (cf.Operator == "or")
                {
                    n = new PlNode(Connective.OR);
                }
                else if (cf.Operator == "when")
                {
                    n = new PlNode(Connective.WHEN);
                }
                else
                    throw new NotImplementedException();

                for (int i = 0; i < lSons.Count - 1; i++)
                    lSons[i].next = lSons[i + 1];

                if (lSons.Count == 0)
                    Console.Write("*");

                n.sons = lSons[0];
            }
            else
            { 
                PredicateFormula pf = (PredicateFormula)f;
                n = new PlNode(Connective.ATOM);
                n.atom = Convert(pf.Predicate);
                


                if(pf.Predicate.Negation)
                {
                    PlNode plNot = new PlNode(Connective.NOT);
                    plNot.sons = n;
                    n = plNot;
                }
                    
            }
            return n;
        }

        private TokenList Convert(Predicate p)
        {
            TokenList tl = new TokenList(p.Name);
            TokenList tlCurrent = tl;
            if (p is ParametrizedPredicate pp)
            {
                foreach (Argument arg in pp.Parameters)
                {
                    TokenList tlNew = new TokenList(arg.Name);
                    tlCurrent.next = tlNew;
                    tlCurrent = tlNew;
                }
            }
            else if (p is GroundedPredicate gp)
            {
                foreach (Constant c in gp.Constants)
                {
                    TokenList tlNew = new TokenList(c.Name);
                    tlCurrent.next = tlNew;
                    tlCurrent = tlNew;
                }
            }
            /*
            else if (p is KnowPredicate kp)
            {
                tl = Convert(kp.Knowledge);
                tl.item = p.Name;
            }
            */
            else
                throw new NotImplementedException();
            return tl;
        }

        private void SetConstants(Domain d)
        {
            //constants: gparse_constants
            List<TypedList> lConstants = new List<TypedList>();
            foreach(Constant c in d.Constants)
            {
                TypedList tl = new TypedList(c.Name, c.Type);
                lConstants.Add(tl);
            }
            for (int i = 0; i < lConstants.Count - 1; i++)
                lConstants[i].next = lConstants[i + 1];

            if (lConstants.Count > 0)
                FF.Parsing.gparse_constants = lConstants[0];
            else
                FF.Parsing.gparse_constants = null;
        }

        private List<string> GetTypeHierarchy(string sType, Domain d)
        {
            string sCurrent = sType;
            List<string> hierarchy = new List<string>();
            hierarchy.Add(sType);
            while (d.TypeHierarchy.ContainsKey(sCurrent))
            {
                sCurrent = d.TypeHierarchy[sCurrent];
                hierarchy.Add(sCurrent);
            }
            return hierarchy;
        }

        private void SetTypes(Domain d)
        {
            //types: gparse_types
            List<TypedList> lTypes = new List<TypedList>();
            for(int iType = 0; iType < d.Types.Count; iType++)
            {
                string sType = d.Types[iType];
                if (sType.ToUpper() == Constants.STANDARD_TYPE)
                    sType = Constants.STANDARD_TYPE;
                TypedList tl = new TypedList(sType);
                List<string> lHierarchy = GetTypeHierarchy(sType, d);
                if(lHierarchy.Count > 0)
                {
                    string sLast = lHierarchy[lHierarchy.Count - 1];
                    if (sLast.ToUpper() == Constants.STANDARD_TYPE)
                        lHierarchy.Remove(sLast);
                }
                TokenList tlHierarchy = new TokenList();
                tl.type = tlHierarchy;
                foreach(string sHierarchy in lHierarchy)
                {
                    tlHierarchy.item = sHierarchy;
                    tlHierarchy.next = new TokenList();
                    tlHierarchy = tlHierarchy.next;
                }
                tlHierarchy.item = Constants.STANDARD_TYPE;

                lTypes.Add(tl);
            }



            if (lTypes.Count > 0)
            {
                for (int i = 0; i < lTypes.Count - 1; i++)
                {
                    lTypes[i].next = lTypes[i + 1];
                }
                FF.Parsing.gparse_types = lTypes[0];
            }
            else
            {
                TypedList tl = new TypedList(Constants.STANDARD_TYPE);
                tl.type = new TokenList(Constants.STANDARD_TYPE);
                FF.Parsing.gparse_types = tl;
            }


        }
    }
}
