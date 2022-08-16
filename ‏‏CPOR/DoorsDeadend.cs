using System.IO;

namespace CPOR
{
    class DoorsDeadend
    {
        public int Length { get; private set; }
        public int Width { get; private set; }

        public string Name { get { return "Doors&" + Length + "&" + Width; } }
        public DoorsDeadend(int iLength, int iWidth)
        {
            Length = iLength;
            Width = iWidth;
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
            sDomain += "(problem " + Name + ")\n";
            sDomain += "(:domain " + Name + ")\n";
            sDomain += GetInitState();
            sDomain += "(:goal (and (at " + GetPosition(Length, Width / 2) + ")))\n";
            sDomain += ")";
            return sDomain;
        }


        public void WriteDeadends(string sPath)
        {
            if (!Directory.Exists(sPath))
            {
                Directory.CreateDirectory(sPath);
            }
            StreamWriter swProblem = new StreamWriter(sPath + "/dead.pddl");
            swProblem.WriteLine("(define (problem deadends_" + Name + ")");
            swProblem.WriteLine("  (:domain " + Name + ")");
            swProblem.WriteLine("(:init ");

            for (int iX = 1; iX <= Length; iX++)
            {
                if (iX % 2 == 0)
                {
                    swProblem.WriteLine("\t(and (not (key-at " + GetPosition(iX - 1, 1) + ")) (all-locked-" + iX + "))\n");
                }
            }


            swProblem.WriteLine("))");
            swProblem.Close();
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
            for (int iX = 1; iX <= Length; iX++)
            {
                for (int iY = 1; iY <= Width; iY++)
                {
                    if (iX > 1)
                        sAdjacents += GetAdjacent(iX, iY, iX - 1, iY);
                    if (iX < Length)
                        sAdjacents += GetAdjacent(iX, iY, iX + 1, iY);
                    if (iY > 1)
                        sAdjacents += GetAdjacent(iX, iY, iX, iY - 1);
                    if (iY < Width)
                        sAdjacents += GetAdjacent(iX, iY, iX, iY + 1);
                }
            }
            return sAdjacents;
        }

        private string GetInitState()
        {
            string sInit = "(:init\n";
            sInit += "(and\n";
            sInit += "(at " + GetPosition(1, 1) + ")" + "\n";
            sInit += GetAdjacents() + "\n";
            sInit += GetOpened() + "\n";
            sInit += ")\n)\n";
            return sInit;
        }

        private string GetOpened()
        {
            string sOpened = "";
            for (int iX = 1; iX <= Length; iX++)
            {
                if (iX % 2 == 0)
                {
                    sOpened += "(oneof  \n";
                }
                for (int iY = 1; iY <= Width; iY++)
                {
                    if (iX % 2 == 0)
                        sOpened += "\t";
                    sOpened += "(opened " + GetPosition(iX, iY) + ")\n";
                }
                if (iX % 2 == 0)
                {
                    sOpened += "\t(all-locked-" + iX + ")";
                    sOpened += ")\n";
                    sOpened += "(unknown (key-at " + GetPosition(iX - 1, 1) + "))\n";
                }
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

        private void GenerateDomain(StreamWriter sw)
        {
            sw.Write("(define \n");
            sw.Write("(domain " + Name + ")\n");
            sw.Write("(:types POS)\n");
            sw.Write(GenerateConstants() + "\n");
            sw.Write(GeneratePredicates());
            GenerateActions(sw);
            sw.Write(")");
        }

        private void GenerateActions(StreamWriter sw)
        {
            sw.WriteLine(GenerateMoveAction());
            sw.WriteLine(GenerateUnlockAction());
            sw.WriteLine(GenerateSenseDoor());
            sw.WriteLine(GenerateSenseKey());
        }

        private string GenerateMoveAction()
        {
            string sAction = "(:action move\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";

            sAction += "\t:precondition (and (adj ?i ?j) (at ?i) (opened ?j))\n";
            sAction += "\t:effect (and (not (at ?i)) (at ?j))";


            sAction += ")\n";
            return sAction;
        }
        private string GenerateUnlockAction()
        {
            string sAction = "(:action unlock\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";

            sAction += "\t:precondition (and (adj ?i ?j) (at ?i) (key-at ?i))\n";
            sAction += "\t:effect (opened ?j)";


            sAction += ")\n";
            return sAction;
        }

        private string GenerateSenseDoor()
        {
            string sAction = "(:action sense-door\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            sAction += "\t:precondition (and (adj ?i ?j) (at ?i))\n";
            sAction += "\t:observe (opened ?j)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateSenseKey()
        {
            string sAction = "(:action sense-key\n";
            sAction += "\t:parameters (?i - pos)\n";
            sAction += "\t:precondition (at ?i)\n";
            sAction += "\t:observe (key-at ?i)\n";
            sAction += ")\n";
            return sAction;
        }

        private string GenerateConstants()
        {
            string sConstants = "(:constants";
            for (int i = 1; i <= Length; i++)
                for (int j = 1; j <= Width; j++)
                    sConstants += " p" + i + "-" + j;
            sConstants += " - pos";

            sConstants += ")\n";
            return sConstants;
        }

        private string GeneratePredicates()
        {
            string sPredictes = "(:predicates\n";
            sPredictes += "\t(adj ?i ?j - pos)\n";
            sPredictes += "\t(at ?i - pos)\n";
            sPredictes += "\t(opened ?i - pos)\n";
            sPredictes += "\t(key-at  ?i - pos)\n";
            for (int i = 1; i <= Length; i++)
                sPredictes += "\t(all-locked-" + i + ")\n";
            sPredictes += ")\n";
            return sPredictes;
        }

    }
}
