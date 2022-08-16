using System.IO;

namespace CPOR
{
    class CanadianTravelingSalesPerson
    {
        public int Length { get; private set; }
        public int Width { get; private set; }
        public int LongRangeSensingCost { get; private set; }

        private bool[,,] m_aEdges;

        public CanadianTravelingSalesPerson(int iLength, int iWidth, int iLongRangeSensingCost)
        {
            Length = iLength;
            Width = iWidth;
            LongRangeSensingCost = iLongRangeSensingCost;
            m_aEdges = new bool[Length, Width, Width];
            InitEdges(3);
        }

        private void InitEdges(int iMaxEdges)
        {
            int i = 0, j = 0;
            for (i = 0; i < Length; i++)
            {
                for (j = 0; j < Width; j++)
                {
                    int iEdges = RandomGenerator.Next(iMaxEdges - 1) + 1;
                    while (iEdges > 0)
                    {
                        int iEdge = RandomGenerator.Next(Width);
                        if (!m_aEdges[i, j, iEdge])
                        {
                            m_aEdges[i, j, iEdge] = true;
                            iEdges--;
                        }
                    }
                }
            }
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
            sDomain += "(problem CTSP-" + Length + "-" + Width + ")\n";
            sDomain += "(:domain CTSP-" + Length + "-" + Width + ")\n";
            sDomain += "(:goal (and (got-the-treasure)))\n";
            sDomain += "(:metric minimize (cost))\n";
            sDomain += GetInitState();
            sDomain += ")";
            return sDomain;
        }

        private string GetPosition(int iX, int iY)
        {
            return "p" + iX + "-" + iY;
        }
        private string GetEdge(int iX1, int iY1, int iX2, int iY2)
        {
            return "(edge " + GetPosition(iX1, iY1) + " " + GetPosition(iX2, iY2) + ")\n";
        }
        private string GetEdges()
        {
            string sEdges = "";
            int i = 0, j = 0;
            for (i = 0; i < Length; i++)
            {
                for (j = 0; j < Width; j++)
                {
                    for (int k = 0; k < Width; k++)
                    {
                        if (m_aEdges[i, j, k])
                        {
                            sEdges += GetEdge(i, j, i + 1, k);
                            sEdges += GetEdge(i + 1, k, i, j);
                        }
                    }

                }
            }
            return sEdges;
        }
        private string GetGoldLocations()
        {
            string sGold = "";
            for (int i = 0; i < Width; i++)
            {
                sGold += "(gold-at p" + Length + "-" + i + ")" + "\n";
            }
            return sGold;
        }

        private string GetInitState()
        {
            string sInit = "(:init\n";
            sInit += "(and\n";
            sInit += "(at p1-1)" + "\n";
            sInit += GetGoldLocations();
            sInit += GetEdges() + "\n";
            sInit += GetOpen() + "\n";
            sInit += GetFragile() + "\n";
            sInit += "(= (cost) 0)\n";
            sInit += ")\n)\n";
            return sInit;
        }

        private string GetOpen()
        {
            string sOpenClose = "";
            int i = 0, j = 0;
            for (i = 0; i < Length; i++)
            {
                for (j = 0; j < Width; j++)
                {
                    for (int k = 0; k < Width; k++)
                    {
                        if (m_aEdges[i, j, k])
                        {
                            sOpenClose += "(oneof (open " + GetPosition(i, j) + " " + GetPosition(i + 1, k) + ")";
                            sOpenClose += "    (not (open " + GetPosition(i, j) + " " + GetPosition(i + 1, k) + ")))\n";
                            sOpenClose += "(oneof (open " + GetPosition(i + 1, k) + " " + GetPosition(i, j) + ")";
                            sOpenClose += "    (not (open " + GetPosition(i + 1, k) + " " + GetPosition(i, j) + ")))\n";
                        }
                    }
                }
            }
            return sOpenClose;
        }
        private string GetFragile()
        {
            string sOpenClose = "";
            int i = 0, j = 0;
            for (i = 0; i < Length; i++)
            {
                for (j = 0; j < Width; j++)
                {
                    for (int k = 0; k < Width; k++)
                    {
                        if (m_aEdges[i, j, k])
                        {
                            sOpenClose += "(oneof (fragile " + GetPosition(i, j) + " " + GetPosition(i + 1, k) + ")";
                            sOpenClose += "    (not (fragile " + GetPosition(i, j) + " " + GetPosition(i + 1, k) + ")))\n";
                            sOpenClose += "(oneof (fragile " + GetPosition(i + 1, k) + " " + GetPosition(i, j) + ")";
                            sOpenClose += "    (not (fragile " + GetPosition(i + 1, k) + " " + GetPosition(i, j) + ")))\n";
                        }
                    }
                }
            }
            return sOpenClose;
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
            sw.Write(GenerateFunctions());
            GenerateActions(sw);
            sw.Write(")");
        }

        private string GenerateFunctions()
        {
            return "(:functions (cost))\n";
        }

        private void GenerateActions(StreamWriter sw)
        {
            sw.WriteLine(GenerateMoveAction());
            sw.WriteLine(GenerateObserveLocationAction());
            sw.WriteLine(GenerateSenseOpenRemoteAction());
            sw.WriteLine(GenerateSenseFragileLocalAction());
            sw.WriteLine(GenerateSenseFragileRemoteAction());
            sw.WriteLine(GenerateSenseOpenLocalAction());
            sw.WriteLine(GenerateGrabAction());
            sw.WriteLine(GenerateOpenEdgeAction());
            sw.WriteLine(GenerateWarmSensorAction());
        }
        private string GenerateGrabAction()
        {
            string sAction = "(:action grab\n";
            sAction += "\t:parameters (?i - pos)\n";
            sAction += "\t:precondition (and (gold-at ?i) (at ?i))\n";
            sAction += "\t:effect (and (got-the-treasure) (not (gold-at ?i)))\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateWarmSensorAction()
        {
            string sAction = "(:action warm-sensor\n";
            sAction += "\t:effect (and \n";
            sAction += "\t(sensor-warm)\n";
            sAction += "\t(increase (cost) " + LongRangeSensingCost + ")";
            sAction += "\t)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateMoveAction()
        {
            string sAction = "(:action move\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            sAction += "\t:precondition (and (edge ?i ?j) (at ?i))\n";
            //sAction += "\t:effect (and (not (at ?i)) (at ?j))\n";         
            sAction += "\t:effect (and\n";
            sAction += "\t\t(increase (cost) 1)\n";
            sAction += "\t\t(not (sensor-warm))\n";
            sAction += "\t\t(when (and (fragile ?i ?j) (open ?i ?j))\n";
            sAction += "\t\t\t(oneof (and (not (at ?i)) (at ?j)) (not (open ?i ?j))))";
            sAction += "\t\t(when (and (not (fragile ?i ?j)) (open ?i ?j))\n";
            sAction += "\t\t\t(and (not (at ?i)) (at ?j))))";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateOpenEdgeAction()
        {
            string sAction = "(:action open-edge\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            sAction += "\t:precondition (and (edge ?i ?j) (at ?i))\n";
            //sAction += "\t:effect (and (not (at ?i)) (at ?j))\n";         
            sAction += "\t:effect (and\n";
            sAction += "\t\t(increase (cost) 10)\n";
            sAction += "\t\t(open ?i ?j))";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateSenseOpenLocalAction()
        {
            string sAction = "(:action sense-open-local\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            sAction += "\t:precondition (and (at ?i) (edge ?i ?j))\n";
            sAction += "\t:observe (open ?i ?j)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateSenseOpenRemoteAction()
        {
            string sAction = "";
            sAction += "(:action sense-open-remote\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            sAction += "\t:precondition (and (edge ?i ?j) (sensor-warm))\n";
            //sAction += "\t:effect (increase (cost) " + LongRangeSensingCost + ")\n";
            sAction += "\t:observe (open ?i ?j)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateSenseFragileLocalAction()
        {
            string sAction = "(:action sense-fragile-local\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            sAction += "\t:precondition (and (at ?i) (edge ?i ?j))\n";
            sAction += "\t:observe (fragile ?i ?j)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateSenseFragileRemoteAction()
        {
            string sAction = "";
            sAction += "(:action sense-fragile-remote\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            sAction += "\t:precondition (and (edge ?i ?j) (sensor-warm))\n";
            //sAction += "\t:effect (increase (cost) " + LongRangeSensingCost + ")\n";
            sAction += "\t:observe (fragile ?i ?j)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateObserveLocationAction()
        {
            string sAction = "(:action observe-location\n";
            sAction += "\t:parameters (?i - pos)\n";
            sAction += "\t:observe (at ?i)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateConstants()
        {
            string sConstants = "(:constants";
            for (int i = 0; i <= Length; i++)
                for (int j = 0; j < Width; j++)
                    sConstants += " p" + i + "-" + j;
            sConstants += " - pos";
            sConstants += ")\n";
            return sConstants;
        }

        private string GeneratePredicates()
        {
            string sPredictes = "(:predicates\n";
            sPredictes += "\t(edge ?i ?j - pos)\n";
            sPredictes += "\t(open ?i ?j - pos)\n";
            sPredictes += "\t(fragile ?i ?j - pos)\n";
            sPredictes += "\t(at ?i - pos)\n";
            sPredictes += "\t(gold-at ?i - pos)\n";
            sPredictes += "\t(got-the-treasure)\n";
            sPredictes += "\t(sensor-warm)\n";
            sPredictes += ")\n";
            return sPredictes;
        }

        public string Name { get { return "CTSP-" + Length + "-" + Width; } }
    }
}
