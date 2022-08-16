using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace CPOR
{
    class MineSweeper
    {
        public static int Size { get; private set; }
        public MineSweeper(int iSize)
        {
            Size = iSize;
        }
        public void WriteProblem(string sPath)
        {
            StreamWriter sw = new StreamWriter(sPath + @"\p.pddl");
            GenerateProblem(sw);
            sw.Close();
        }


        private void GenerateProblem(StreamWriter sw)
        {
            string sProblem = "(define \n";
            sProblem += "(problem LargeMineSweeper-" + Size + ")\n";
            sProblem += "(:domain LargeMineSweeper-" + Size + ")\n";
            sProblem += "(:goal (and\n";

            for (int iX = 0; iX < Size; iX++)
                for (int iY = 0; iY < Size; iY++)
                {
                    sProblem += "\t(oneof (flagged " + GetPosition(iX, iY) + ") (not (mine-at " + GetPosition(iX, iY) + ")))\n";
                }

            sProblem += "))\n";
            sw.WriteLine(sProblem);

            WriteInitState(sw);

            sw.WriteLine(")");

        }

        private string GetPosition(int iX, int iY)
        {
            return "p" + iX + "-" + iY;
        }
        private void WriteInitState(StreamWriter sw)
        {
            sw.WriteLine("(:init");
            sw.WriteLine("(and");
            for (int iX = 0; iX < Size; iX++)
                for (int iY = 0; iY < Size; iY++)
                {
                    sw.WriteLine("\t(unknown (mine-at " + GetPosition(iX, iY) + "))");
                }
            //trying not to put the number of mines into the initial state but in actions - will try the other way round later
            //the above works, but conversion into CNF after the regression is klling me. Trying putting the clauses into the initial state.
            //the init state below doesn't give me sufficient power, going back to no init state

            for (int iX = 0; iX < Size; iX++)
                for (int iY = 0; iY < Size; iY++)
                {
                    string sOneValue = "(oneof";
                    for (int i = 0; i < 9; i++)
                        sOneValue += " (mine-count " + GetPosition(iX, iY) + " v" + i + ")";
                    sOneValue += ")";
                    sw.WriteLine(sOneValue);
                }
            /*
                              List<string> lNeighbors = new List<string>();
                              for (int i = -1; i <= 1; i++)
                                  for (int j = -1; j <= 1; j++)
                                      if (i != 0 || j != 0)
                                          if (iX + i >= 0 && iX + i < Size)
                                              if (iY + j >= 0 && iY + j < Size)
                                                  lNeighbors.Add(GetPosition(iX + i, iY + j));

                              int cSubsets = (int)Math.Pow(2, lNeighbors.Count);
                              for (int iSubset = 0 ; iSubset < cSubsets ; iSubset++)
                              {
                                  //p->q = -p or q
                                  string sClause = "\t (or ";
                                  int iTemp = iSubset;
                                  int cMines = 0;
                                  for (int i = 0; i < lNeighbors.Count; i++)
                                  {
                                      if (iTemp % 2 == 1)
                                      {
                                          sClause += " (not (mine-at " + lNeighbors[i] + "))";
                                          cMines++;
                                      }
                                      else
                                          sClause += " (mine-at " + lNeighbors[i] + ")";
                                      iTemp /= 2;
                                  }
                                  sClause += " (mine-count " + GetPosition(iX, iY) + " v" + cMines + "))";
                                  sw.WriteLine( sClause);
                              }
                          }
                       * */
            sw.WriteLine(")\n)");
        }

        public void WriteDomain(string sPath)
        {
            if (!Directory.Exists(sPath))
                Directory.CreateDirectory(sPath);
            StreamWriter sw = new StreamWriter(sPath + @"\d.pddl");
            GenerateDomain(sw);
            sw.Close();
        }

        private void GenerateDomain(StreamWriter sw)
        {
            sw.Write("(define \n");
            sw.Write("(domain " + Name + ")\n");
            sw.Write("(:types pos value)\n");
            sw.Write(GenerateConstants() + "\n");
            sw.Write(GeneratePredicates());
            GenerateActions(sw);
            sw.Write(")");
        }

        private void GenerateActions(StreamWriter sw)
        {
            sw.WriteLine(GenerateFlagCellAction());
            sw.WriteLine(GenerateObserveMinesCellAction());
            sw.WriteLine(ObserveDead());
            //the init state is not providing sufficiet power, going back to conditional effects
            //sw.WriteLine(GenerateSimpleOpenCellAction());

            //works, but after the regression, conversion into CNF is killing me
            for (int iX = 0; iX < Size; iX++)
                for (int iY = 0; iY < Size; iY++)
                {
                    sw.WriteLine(GenerateOpenCellAction(iX, iY));
                }

        }

        private string ObserveDead()
        {
            string sAction = "(:action observe-dead\n";
            string sObserve = "\t:observe (dead)\n";
            sAction += sObserve;
            sAction += ")\n";
            return sAction;
        }

        private string GenerateObserveMinesCellAction()
        {
            string sAction = "(:action observe-mine-count\n";
            string sParameters = "\t:parameters (?p - pos ?v - value)\n";
            string sPrecondition = "\t:precondition (and (not (dead)) (opened ?p))\n";
            string sObserve = "\t:observe (mine-count ?p  ?v)\n";
            sAction += sParameters;
            sAction += sPrecondition;
            sAction += sObserve;
            sAction += ")\n";
            return sAction;
        }
        //works, but after the regression, conversion into CNF is killing me
        private string GenerateOpenCellAction(int iX, int iY)
        {
            string sAction = "(:action open-cell-" + iX + "-" + iY + "\n";
            sAction += "\t:precondition (not (dead))\n";
            sAction += "\t:effect (and (opened " + GetPosition(iX, iY) + ")\n";

            List<string> lNeighbors = new List<string>();
            for (int i = -1; i <= 1; i++)
                for (int j = -1; j <= 1; j++)
                    if (i != 0 || j != 0)
                        if (iX + i >= 0 && iX + i < Size)
                            if (iY + j >= 0 && iY + j < Size)
                                lNeighbors.Add(GetPosition(iX + i, iY + j));
            List<List<string>> lSubsets = GetAllSubsets(lNeighbors, 0);
            sAction += "\t(when (mine-at " + GetPosition(iX, iY) + ") (dead))\n";
            foreach (List<string> lSubset in lSubsets)
            {
                string sWhen = "\t (when (and";
                foreach (string sMine in lSubset)
                    sWhen += " (mine-at " + sMine + ")";
                foreach (string sNoMine in lNeighbors)
                    if (!lSubset.Contains(sNoMine))
                        sWhen += " (not (mine-at " + sNoMine + "))";
                sWhen += ") (mine-count " + GetPosition(iX, iY) + " v" + lSubset.Count + "))\n";
                sAction += sWhen;
            }
            sAction += "))\n";
            return sAction;
        }

        private string GenerateSimpleOpenCellAction()
        {
            string sAction = "(:action open-cell\n";
            sAction += "\t:parameters (?p - pos)\n";
            sAction += "\t:precondition (not (dead))\n";
            sAction += "\t:effect (and (opened ?p)\n";

            sAction += "\t(when (mine-at ?p) (dead))\n";

            sAction += "))\n";
            return sAction;
        }

        private List<List<string>> GetAllSubsets(List<string> l, int iCurrent)
        {
            List<List<string>> lResult = new List<List<string>>();
            if (iCurrent == l.Count)
            {
                lResult.Add(new List<string>());
            }
            else
            {
                List<List<string>> lRest = GetAllSubsets(l, iCurrent + 1);
                foreach (List<string> lr in lRest)
                {
                    lResult.Add(lr);
                    List<string> lrplus = new List<string>(lr);
                    lrplus.Add(l[iCurrent]);
                    lResult.Add(lrplus);

                }
            }
            return lResult;
        }

        private string GenerateFlagCellAction()
        {
            string sAction = "(:action flag\n";
            string sParameters = "\t:parameters (?p - pos)\n";
            string sPrecondition = "\t:precondition (and (not (dead)) (mine-at ?p))\n";
            string sEffect = "\t:effect (flagged ?p)\n";
            sAction += sParameters;
            sAction += sPrecondition;
            sAction += sEffect;
            sAction += ")\n";
            return sAction;
        }


        private string GenerateConstants()
        {
            string sConstants = "(:constants";
            for (int i = 0; i < Size; i++)
                for (int j = 0; j < Size; j++)
                    sConstants += " " + GetPosition(i, j);
            sConstants += " - pos\n";

            for (int i = 0; i < 9; i++)
                sConstants += " v" + i;
            sConstants += " - value\n";

            sConstants += ")\n";
            return sConstants;
        }

        private string GeneratePredicates()
        {
            string sPredictes = "(:predicates\n";
            sPredictes += "\t(mine-at ?p - pos)\n";
            sPredictes += "\t(flagged ?p - pos)\n";
            sPredictes += "\t(opened ?p - pos)\n";
            sPredictes += "\t(dead)\n";
            sPredictes += "\t(mine-count ?p - pos ?v - value)\n";
            sPredictes += ")\n";
            return sPredictes;
        }

        public string Name { get { return "LargeMineSweeper-" + Size; } }



        static HashSet<int> VisitedLocations = new HashSet<int>();

        private static GroundedPredicate GetPredicate(string sName, int iX, int iY)
        {
            GroundedPredicate gpSafe = new GroundedPredicate(sName);
            gpSafe.AddConstant(new Constant("pos", "p" + iX + "-" + iY));
            return gpSafe;

        }

        public static int Shootings = 0;
        public static List<string> MineSweeperHeuristic(PartiallySpecifiedState pssCurrent, Domain d, Formula fObserve)
        {
            int[,] aBoard;
            aBoard = new int[Size, Size];
            List<string> lActions = new List<string>();
            List<int> lUnknown = new List<int>();

            for (int iX = 0; iX < Size; iX++)
            {
                for (int iY = 0; iY < Size; iY++)
                {
                    GroundedPredicate gp = GetPredicate("opened", iX, iY);
                    if (pssCurrent.Observed.Contains(gp))
                    {
                        aBoard[iX, iY] = 1;//opened
                    }
                    else
                    {

                        gp = GetPredicate("mine-at", iX, iY);
                        if (pssCurrent.Observed.Contains(gp))
                        {
                            gp = GetPredicate("flagged", iX, iY);
                            if (pssCurrent.Observed.Contains(gp))
                                aBoard[iX, iY] = 4;//flagged mine
                            else
                                aBoard[iX, iY] = 2;//unflagged mine
                        }
                        else if (pssCurrent.Observed.Contains(gp.Negate()))
                            aBoard[iX, iY] = 3;//no mine
                    }
                }
            }




            List<int> lCandidates = new List<int>();
            for (int iX = 0; iX < Size; iX++)
            {
                for (int iY = 0; iY < Size; iY++)
                {
                    if (aBoard[iX, iY] == 0 || aBoard[iX, iY] == 3)
                    {
                        lCandidates.Add((iX) * 1000 + iY);
                    }
                    else if (aBoard[iX, iY] == 2)
                        lActions.Add("flag p" + iX + "-" + iY);
                }
            }

            if (lCandidates.Count > 0)
            {
                int iChosen = lCandidates[RandomGenerator.Next(lCandidates.Count)];
                int iChosenX = iChosen / 1000;
                int iChosenY = iChosen % 1000;
                lActions.Add("open-cell-" + iChosenX + "-" + iChosenY);
                //lActions.Add("open-cell p" + iChosenX + "-" + iChosenY);
                lActions.Add("observe-dead");
                for (int i = 0; i < 9; i++)
                    lActions.Add("observe-mine-count p" + iChosenX + "-" + iChosenY + " v" + i);
                Shootings++;
            }
            /*
        else if (lUnknown.Count > 0)
        {
            int iChosen = lUnknown[RandomGenerator.Next(lUnknown.Count)];
            int iChosenX = iChosen / 1000;
            int iChosenY = iChosen % 1000;
            lActions.Add("shoot p-" + iChosenX + " p-" + iChosenY);
            Shootings++;
        }
        */



            return lActions;
        }


    }
}
