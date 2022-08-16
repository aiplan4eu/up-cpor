using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace CPOR
{
    class MasterMind
    {
        public int Colors { get; private set; }
        public int Pegs { get; private set; }
        public int GuessCost { get; private set; }
        public MasterMind(int cColors, int cPegs, int iGuessCost)
        {
            GuessCost = iGuessCost;
            Colors = cColors;
            Pegs = cPegs;
            if (Pegs > Colors)
                throw new InvalidOperationException();
        }
        public void WriteProblem(string sPathName)
        {
            StreamWriter sw = new StreamWriter(sPathName + @"\p.pddl");
            sw.WriteLine(GenerateProblem());
            sw.Close();
        }

        private string GenerateProblem()
        {
            string sProblem = "(define \n";
            sProblem += "(problem MasterMind-" + Colors + "-" + Pegs + ")\n";
            sProblem += "(:domain MasterMind-" + Colors + "-" + Pegs + ")\n";
            //sProblem += GenerateObjects() + "\n";
            sProblem += GetInitState() + "\n";
            sProblem += "(:goal (and (LocationHits v" + Pegs + ")))\n";
            sProblem += ")";
            return sProblem;
        }

        private string GenerateObjects()
        {
            int iPeg = 0, iColor = 0;
            string sObjects = "(:objects\n";
            for (iPeg = 0; iPeg < Pegs; iPeg++)
            {
                sObjects += "\t p" + iPeg + " - PEG\n";
            }
            for (iColor = 0; iColor < Colors; iColor++)
            {
                sObjects += "\t c" + iColor + " - COLOR\n";
            }
            for (iPeg = 0; iPeg <= Pegs; iPeg++)
            {
                sObjects += "\t v" + iPeg + " - VALUE\n";
            }
            if (GuessCost > 0)
            {
                for (int iGuessStep = 0; iGuessStep < GuessCost; iGuessStep++)
                    sObjects += "\t gs" + iGuessStep + " - GUESSSTEP\n";
            }
            sObjects += ")";
            return sObjects;
        }

        private string GenerateConstants()
        {
            int iPeg = 0, iColor = 0;
            string sObjects = "(:constants\n";
            for (iPeg = 0; iPeg < Pegs; iPeg++)
            {
                sObjects += "\t p" + iPeg + " - PEG\n";
            }
            for (iColor = 0; iColor < Colors; iColor++)
            {
                sObjects += "\t c" + iColor + " - COLOR\n";
            }
            for (iPeg = 0; iPeg <= Pegs; iPeg++)
            {
                sObjects += "\t v" + iPeg + " - VALUE\n";
            }
            if (GuessCost > 0)
            {
                for (int iGuessStep = 0; iGuessStep < GuessCost; iGuessStep++)
                    sObjects += "\t gs" + iGuessStep + " - GUESSSTEP\n";
            }
            sObjects += ")";
            return sObjects;
        }

        private string GetInitState()
        {
            int iPeg = 0;
            string sInit = "(:init\n";
            sInit += "(and\n";
            //sInit += "(LocationHits v0)\n";
            //sInit += "(ColorHits v0)\n";
            for (iPeg = 0; iPeg < Pegs; iPeg++)
            {
                //sInit += "(NColorhit p" + iPeg + ") (NLocationHit p" + iPeg + ")\n";
            }
            sInit += "\t(Nguessed)\n";
            if (GuessCost > 0)
                sInit += "(Guess-Step gs0)";
            sInit += OneColorOnEachPeg();
            sInit += ForbidRepeatedColors();
            sInit += ")\n)\n";
            return sInit;
        }

        private string ForbidRepeatedColors()
        {
            int iPeg = 0, iColor = 0;
            string sColorStatement = "", sFullStatement = "";
            for (iColor = 0; iColor < Colors; iColor++)
            {
                sColorStatement = "\t(oneof";
                for (iPeg = 0; iPeg < Pegs; iPeg++)
                {
                    sColorStatement += " (on p" + iPeg + " c" + iColor + ")";
                }
                //sColorStatement += " (not (used c" + iColor + ")))";
                sColorStatement += " (out c" + iColor + "))";
                sFullStatement += sColorStatement + "\n";
            }
            return sFullStatement;
        }

        private string OneColorOnEachPeg()
        {
            int iPeg = 0, iColor = 0;
            string sPegStatement = "", sFullStatement = "";
            for (iPeg = 0; iPeg < Pegs; iPeg++)
            {
                sPegStatement = "\t(oneof";
                for (iColor = 0; iColor < Colors; iColor++)
                {
                    sPegStatement += " (on p" + iPeg + " c" + iColor + ")";
                }
                sPegStatement += ")";
                sFullStatement += sPegStatement + "\n";
            }
            return sFullStatement;
        }

        private string GeneratePredicates()
        {
            string sPredicates = "(:predicates\n";
            sPredicates += "\t(LocationHits ?v - VALUE)\n";
            sPredicates += "\t(ColorHits ?v - VALUE)\n";
            sPredicates += "\t(on ?p - PEG ?c - COLOR)\n";
            sPredicates += "\t(out ?c - COLOR)\n";
            //sPredicates += "\t(used ?c - COLOR)\n";
            sPredicates += "\t(guess ?p - PEG ?c - COLOR)\n";
            sPredicates += "\t(LocationHit ?p - PEG)\n";
            //sPredicates += "\t(NLocationHit ?p - PEG)\n";//NLocationHit used to avoid negative preconditions
            sPredicates += "\t(ColorHit ?p - PEG)\n";
            //sPredicates += "\t(NColorHit ?p - PEG)\n"; //NColorHit used to avoid negative preconditions
            sPredicates += "\t(guessed)\n";
            sPredicates += "\t(Nguessed)\n";
            if (GuessCost > 0)
            {
                sPredicates += "\t(Guess-Step ?gs - GUESSSTEP)\n";
            }
            sPredicates += ")\n";
            return sPredicates;
        }


        private string GenerateActions()
        {
            string sActions = "";
            if (GuessCost == 0)
                sActions += GenerateGuessAction() + "\n";
            else
                sActions += GenerateGuessActionsWithCost() + "\n";
            sActions += GenerateEvaluateGuessAction() + "\n";
            sActions += GenerateObservationActions() + "\n";
            return sActions;
        }

        private string GenerateGuessActionsWithCost()
        {
            string sActions = "";
            for (int iCost = 0; iCost < GuessCost; iCost++)
            {
                int iPeg = 0;
                string sAction = "(:action guess-all-" + iCost + "\n";
                if (iCost == GuessCost - 1)
                {
                    sAction += ":parameters (";
                    for (iPeg = 0; iPeg < Pegs; iPeg++)
                        sAction += " ?c" + iPeg + " - COLOR";
                    sAction += ")\n";
                }
                sAction += ":precondition (and (Nguessed) (Guess-Step gs" + iCost + "))\n";
                sAction += ":effect (and (not (Guess-Step gs" + iCost + ")) ";
                if (iCost < GuessCost - 1)
                    sAction += "(Guess-Step gs" + (iCost + 1) + ")";
                else
                {
                    sAction += "(guessed) (not (Nguessed)) (Guess-Step gs0)\n";
                    for (iPeg = 0; iPeg <= Pegs; iPeg++)
                    {
                        sAction += "\t(not (LocationHits v" + iPeg + ")) (not (ColorHits v" + iPeg + "))\n";
                    }
                    //LocationHits
                    for (iPeg = 0; iPeg < Pegs; iPeg++)
                    {
                        sAction += "\t(when (on p" + iPeg + " ?c" + iPeg + ") (LocationHit p" + iPeg + "))\n";
                        sAction += "\t(when (not (on p" + iPeg + " ?c" + iPeg + ")) (not (LocationHit p" + iPeg + ")))\n";
                        //sAction += "\t(when (on p" + iPeg + " ?c" + iPeg + ") (and (LocationHit p" + iPeg + ") (not (NLocationHit p" + iPeg + "))))\n";
                    }
                    //ColorHit  - we can use the "out" predicate to reduce complexity
                    for (iPeg = 0; iPeg < Pegs; iPeg++)
                    {
                        //sAction += "\t(when (used ?c" + iPeg + ") (and (ColorHit p" + iPeg + ") (not (NColorHit p" + iPeg + "))))\n"; // CLG does not like negative preconditions
                        sAction += "\t(when (not (out ?c" + iPeg + ")) (ColorHit p" + iPeg + "))\n"; // CLG does not like negative preconditions
                        sAction += "\t(when (out ?c" + iPeg + ") (not (ColorHit p" + iPeg + ")))\n"; // CLG does not like negative preconditions

                    }
                }
                sAction += ")\n";
                sAction += ")\n";
                sActions += sAction;
            }
            return sActions;
        }




        private string GenerateGuessAction()
        {
            int iPeg = 0;
            string sAction = "(:action guess-all\n";
            sAction += ":parameters (";
            for (iPeg = 0; iPeg < Pegs; iPeg++)
                sAction += " ?c" + iPeg + " - COLOR";
            sAction += ")\n";
            //sAction += ":precondition (not (guessed))\n";
            sAction += ":precondition (Nguessed)\n";
            sAction += ":effect (and (guessed) (not (Nguessed))\n";
            for (iPeg = 0; iPeg <= Pegs; iPeg++)
            {
                sAction += "\t(not (LocationHits v" + iPeg + ")) (not (ColorHits v" + iPeg + "))\n";
            }
            //LocationHits
            for (iPeg = 0; iPeg < Pegs; iPeg++)
            {
                sAction += "\t(when (on p" + iPeg + " ?c" + iPeg + ") (LocationHit p" + iPeg + "))\n";
                //sAction += "\t(when (on p" + iPeg + " ?c" + iPeg + ") (and (LocationHit p" + iPeg + ") (not (NLocationHit p" + iPeg + "))))\n";
            }
            //ColorHit  - we can use the "out" predicate to reduce complexity
            for (iPeg = 0; iPeg < Pegs; iPeg++)
            {
                //sAction += "\t(when (used ?c" + iPeg + ") (and (ColorHit p" + iPeg + ") (not (NColorHit p" + iPeg + "))))\n"; // CLG does not like negative preconditions
                sAction += "\t(when (not (out ?c" + iPeg + ")) (ColorHit p" + iPeg + "))\n"; // CLG does not like negative preconditions
                /* CLG doesn't like this either...
                sAction += "\t(when (or";
                for (int iOtherPeg = 0; iOtherPeg < Pegs; iOtherPeg++)
                {
                    sAction += " (on p" + iOtherPeg + " ?c" + iPeg + ")";
                }
                sAction += ") (ColorHit p" + iPeg + "))\n";
                 * */
            }
            sAction += ")\n";
            sAction += ")\n";
            return sAction;
        }

        private string BuildAllCombinations(int iPeg, string sPrefix, string sPredicate, int cHitsInPrefix)
        {
            if (iPeg == Pegs)
            {
                return sPrefix + ") (" + sPredicate + "s v" + cHitsInPrefix + "))\n";
                /* no need to specify everything because they were made false previously
                string sEffect = "(and";
                for (int cHits = 0; cHits <= Pegs; cHits++)
                {
                    string sHits = "(" + sPredicate + "s v" + cHits + ")";
                    if (cHits == cHitsInPrefix)
                    {
                        sEffect += " " + sHits;
                    }
                    else
                    {
                        sEffect += " (not " + sHits + ")";
                    }
                }
                return sPrefix + ") " + sEffect + "))\n";
                 * */
            }
            string sHit = BuildAllCombinations(iPeg + 1, sPrefix + " (" + sPredicate + " p" + iPeg + ")", sPredicate, cHitsInPrefix + 1);
            string sNoHit = BuildAllCombinations(iPeg + 1, sPrefix + " (not (" + sPredicate + " p" + iPeg + "))", sPredicate, cHitsInPrefix);
            //string sNoHit = BuildAllCombinations(iPeg + 1, sPrefix + " (N" + sPredicate + " p" + iPeg + ")", sPredicate, cLocationHits);
            return sHit + sNoHit;
        }

        private string GenerateEvaluateGuessAction()
        {
            int iPeg = 0;
            string sAction = "(:action evaluate-guess\n";
            sAction += ":precondition (guessed)\n";
            sAction += ":effect (and (not (guessed)) (Nguessed)\n";
            for (iPeg = 0; iPeg < Pegs; iPeg++)
            {
                sAction += "\t(not (LocationHit p" + iPeg + ")) (not (ColorHit p" + iPeg + "))\n";
                //sAction += "\t(NLocationHit p" + iPeg + ") (NColorHit p" + iPeg + ")\n";
            }
            //LocationHits
            sAction += BuildAllCombinations(0, "\t(when (and", "LocationHit", 0);
            //ColorHits  - we can use the "out" predicate to reduce complexity
            sAction += BuildAllCombinations(0, "\t(when (and", "ColorHit", 0);
            sAction += ")\n";
            sAction += ")\n";
            return sAction;
        }

        private string GenerateObservationActions()
        {
            string sActions = "(:action observe-LocationHits\n";
            sActions += ":parameters (?v - VALUE)\n";
            sActions += ":observe (LocationHits ?v))\n";

            sActions += "(:action observe-ColorHits\n";
            sActions += ":parameters (?v - VALUE)\n";
            sActions += ":observe (ColorHits ?v))\n";

            return sActions;

        }

        public void WriteDomain(string sPath)
        {
            DirectoryInfo di = new DirectoryInfo(sPath);
            if (!di.Exists)
                di.Create();
            StreamWriter sw = new StreamWriter(sPath + @"\d.pddl");
            sw.Write(GenerateDomain());
            sw.Close();
        }

        private string GenerateDomain()
        {
            string sDomain = "(define \n";
            sDomain += "(domain MasterMind-" + Colors + "-" + Pegs + ")\n";
            sDomain += "(:types PEG COLOR VALUE GUESSSTEP)\n";
            sDomain += GenerateConstants() + "\n";
            sDomain += GeneratePredicates();
            sDomain += GenerateActions();
            sDomain += ")";
            return sDomain;
        }


        public string Name { get { return "MasterMind" + Pegs + "-" + Colors; } }

        public static List<string> MasterMindHeuristic(PartiallySpecifiedState pssCurrent, Domain domain)
        {
            List<Constant> lColors = new List<Constant>();
            List<Constant> lPegs = new List<Constant>();
            List<Constant> lValues = new List<Constant>();
            foreach (Constant c in domain.Constants)
            {
                if (c.Type.ToLower() == "color")
                    lColors.Add(c);
                if (c.Type.ToLower() == "peg")
                    lPegs.Add(c);
                if (c.Type.ToLower() == "value")
                    lValues.Add(c);
            }

            //DateTime dtStart = DateTime.Now;

            //BeliefState bs = pssCurrent.m_bsInitialBelief;

            //State s = bs.ChooseState(true);
            //List<Predicate> l = bs.RunSatSolver();


            //Debug.WriteLine((DateTime.Now - dtStart).TotalSeconds);


            Permute(lColors);
            List<Constant> lGuessColors = new List<Constant>();
            for (int iPeg = 0; iPeg < lPegs.Count; iPeg++)
            {
                /*
                //foreach (GroundedPredicate gp in s.Predicates)
                foreach (GroundedPredicate gp in l)
                {
                    if (gp.ToString().StartsWith("(on p" + iPeg) && gp.Negation == false)
                    {
                        lGuessColors.Add(gp.Constants[1]);
                    }


                }
                */
                foreach (Constant cColor in lColors)
                {
                    GroundedPredicate gp = new GroundedPredicate("on");
                    gp.AddConstant(lPegs[iPeg]);
                    gp.AddConstant(cColor);
                    if (!pssCurrent.Observed.Contains(gp.Negate()))
                    {
                        lGuessColors.Add(cColor);
                        break;
                    }
                }
                lColors.Remove(lGuessColors.Last());

            }
            if (lGuessColors.Count == lPegs.Count)
            {
                List<string> lActions = new List<string>();
                string sGuess = "guess-all";
                foreach (Constant c in lGuessColors)
                    sGuess += " " + c.Name;
                lActions.Add(sGuess);
                lActions.Add("evaluate-guess");
                foreach (Constant cValue in lValues)
                {
                    lActions.Add("observe-LocationHits " + cValue.Name);
                    lActions.Add("observe-ColorHits " + cValue.Name);
                }
                return lActions;
            }
            return null;

        }

        private static void Permute(List<Constant> l)
        {
            for (int i = 0; i < l.Count; i++)
            {
                Constant c = l[i];
                int idx = RandomGenerator.Next(l.Count);
                l[i] = l[idx];
                l[idx] = c;
            }
        }
    }
}
