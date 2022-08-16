using System.IO;

namespace CPOR
{
    class Doors
    {
        public int Size { get; private set; }
        public int MoveCost { get; private set; }
        public Doors(int cSquares, int cMoveSteps)
        {
            Size = cSquares;
            MoveCost = cMoveSteps;
        }
        public void WriteProblem(string sPath)
        {
            StreamWriter sw = new StreamWriter(sPath + @"\p.pddl");
            sw.WriteLine(GenerateProblem());
            sw.Close();
        }


        private string GenerateProblem()
        {
            string sDomain = "(define \n";
            sDomain += "(problem Doors-" + Size + ")\n";
            sDomain += "(:domain Doors-" + Size + ")\n";
            sDomain += GetInitState();
            sDomain += "(:goal (and (at " + GetPosition(Size, Size / 2) + ")))\n";
            sDomain += "(:metric minimize (cost))\n";
            sDomain += ")";
            return sDomain;
        }



        private string GetPosition(int iX, int iY)
        {
            return "p" + iX + "-" + iY;
        }
        private string GetAdjacent(int iX1, int iY1, int iX2, int iY2)
        {
            return "(adj " + GetPosition(iX1, iY1) + " " + GetPosition(iX2, iY2) + ")\n";
        }
        private string GetAdjacents()
        {
            string sAdjacents = "";
            for (int iX = 1; iX <= Size; iX++)
            {
                for (int iY = 1; iY <= Size; iY++)
                {
                    if (iX > 1)
                        sAdjacents += GetAdjacent(iX, iY, iX - 1, iY);
                    if (iX < Size)
                        sAdjacents += GetAdjacent(iX, iY, iX + 1, iY);
                    if (iY > 1)
                        sAdjacents += GetAdjacent(iX, iY, iX, iY - 1);
                    if (iY < Size)
                        sAdjacents += GetAdjacent(iX, iY, iX, iY + 1);
                }
            }
            return sAdjacents;
        }

        private string GetInitState()
        {
            string sInit = "(:init\n";
            sInit += "(and\n";
            sInit += "(at " + GetPosition(1, Size / 2) + ")" + "\n";
            if (MoveCost > 0)
                sInit += "(MoveStep ms0)\n";
            sInit += GetAdjacents() + "\n";
            sInit += GetOpened() + "\n";
            sInit += ")\n)\n";
            return sInit;
        }

        private string GetOpened()
        {
            string sOpened = "";
            for (int iX = 1; iX <= Size; iX++)
            {
                if (iX % 2 == 0)
                    sOpened += "(oneof\n";
                for (int iY = 1; iY <= Size; iY++)
                {
                    if (iX % 2 == 0)
                        sOpened += "\t";
                    sOpened += "(opened " + GetPosition(iX, iY) + ")\n";
                }
                if (iX % 2 == 0)
                    sOpened += ")\n";
            }
            return sOpened;
        }
        public void WriteDomain(string sPath)
        {
            if (!Directory.Exists(sPath))
                Directory.CreateDirectory(sPath);
            StreamWriter sw = new StreamWriter(sPath + @"\d.pddl");
            //sw.Write(GenerateDomain());
            GenerateDomain(sw);
            sw.Close();
        }
        private string GenerateFunctions()
        {
            return "(:functions (cost))\n";
        }

        private void GenerateDomain(StreamWriter sw)
        {
            sw.Write("(define \n");
            sw.Write("(domain " + Name + ")\n");
            if (MoveCost > 0)
                sw.Write("(:types POS MOVE_STEP)\n");
            else
                sw.Write("(:types POS)\n");
            sw.WriteLine(GenerateFunctions());
            sw.Write(GenerateConstants() + "\n");
            sw.Write(GeneratePredicates());
            GenerateActions(sw);
            sw.Write(")");
        }

        private void GenerateActions(StreamWriter sw)
        {
            if (MoveCost > 0)
                sw.WriteLine(GeneratePrepareMoveActions());
            sw.WriteLine(GenerateMoveAction());
            sw.WriteLine(GenerateCheckingAction());
            sw.WriteLine(GenerateSenseDoorLocal());
            sw.WriteLine(GenerateSenseDoorRemote());
        }

        private string GenerateMoveAction()
        {
            string sAction = "(:action move\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            if (MoveCost > 0)
            {
                sAction += "\t:precondition (and (MoveStep ms" + (MoveCost - 1) + ") (adj ?i ?j) (at ?i) (opened ?j))\n";
                sAction += "\t:effect (and (not (MoveStep ms" + (MoveCost - 1) + ")) (MoveStep ms0) (not (at ?i)) (at ?j))\n";
            }
            else
            {
                sAction += "\t:precondition (and (adj ?i ?j) (at ?i) (opened ?j))\n";
                sAction += "\t:effect (and (not (at ?i)) (at ?j)";
                sAction += "\t(increase (cost) 3))\n";
            }

            sAction += ")\n";
            return sAction;
        }
        private string GenerateCheckingAction()
        {
            string sAction = "(:action checking\n";
            sAction += ":effect (and\n";
            for (int iX = 1; iX < Size; iX++)
            {
                if (iX % 2 == 1)
                {
                    for (int iY = 2; iY <= Size - 1; iY++)
                    {
                        for (int iOtherY = 1; iOtherY <= Size; iOtherY++)
                        {
                            string sWhen = "\t(when (and (at " + GetPosition(iX, iY) + ") (opened " + GetPosition(iX + 1, iOtherY) + ")) ";
                            if (iOtherY <= iY)
                                sWhen += "(not (opened-above)))\n";
                            else
                                sWhen += "(opened-above))\n";
                            sAction += sWhen;
                        }
                    }
                }
            }
            sAction += "))\n";
            return sAction;
        }
        private string GeneratePrepareMoveActions()
        {
            string sActions = "";
            string sAction = "";
            for (int iMoveStep = 0; iMoveStep < MoveCost - 1; iMoveStep++)
            {
                sAction = "(:action prepare-move" + iMoveStep + "\n";
                sAction += "\t:precondition (and (MoveStep ms" + iMoveStep + ") (alive))\n";
                sAction += "\t:effect (and (not (MoveStep ms" + iMoveStep + ")) (MoveStep ms" + (iMoveStep + 1) + "))\n";
                sAction += ")\n";
                sActions += sAction;
            }
            return sActions;
        }

        private string GenerateSenseDoorLocal()
        {
            string sAction = "(:action sense-door-local\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            sAction += "\t:precondition (and (adj ?i ?j) (at ?i))\n";
            sAction += "\t:observe (opened ?j)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateSenseDoorRemote()
        {
            string sAction = "(:action sense-door-remote\n";
            sAction += "\t:observe (opened-above)\n";
            sAction += ")\n";
            return sAction;
        }

        private string GenerateConstants()
        {
            string sConstants = "(:constants";
            for (int i = 1; i <= Size; i++)
                for (int j = 1; j <= Size; j++)
                    sConstants += " p" + i + "-" + j;
            sConstants += " - pos";
            if (MoveCost > 0)
            {
                for (int i = 0; i < MoveCost; i++)
                    sConstants += " ms" + i;
                sConstants += " - MOVE_STEP";
            }
            sConstants += ")\n";
            return sConstants;
        }

        private string GeneratePredicates()
        {
            string sPredictes = "(:predicates\n";
            sPredictes += "\t(adj ?i ?j - pos)\n";
            sPredictes += "\t(at ?i - pos)\n";
            sPredictes += "\t(opened ?i - pos)\n";
            sPredictes += "\t(opened-above)\n";
            if (MoveCost > 0)
                sPredictes += "\t(MoveStep ?ms - MOVE_STEP)\n";
            sPredictes += ")\n";
            return sPredictes;
        }

        public string Name { get { return "Doors-" + Size; } }
    }
}
