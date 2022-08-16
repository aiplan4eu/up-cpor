using System.Collections.Generic;
using System.IO;

namespace CPOR
{
    class BoxDomain
    {
        public class Box
        {
            public int X, Y, Weight;
            public int ID;

            public Box(int iX, int iY, int iWeight, int iID)
            {
                X = iX;
                Y = iY;
                Weight = iWeight;
                ID = iID;
            }
        }

        public int Width { get; private set; }
        public int Length { get; private set; }
        public int Agents { get; private set; }
        public List<Box> Boxes { get; private set; }
        public string Name { get; private set; }
        public int[,] Map { get; private set; }
        public BoxDomain(string sBoxDescriptionFile)
        {
            ReadDescriptionFile(sBoxDescriptionFile);
            string sName = sBoxDescriptionFile.Substring(sBoxDescriptionFile.LastIndexOf('\\') + 1);
            sName = sName.Split('.')[0];
            Name = "Box-" + sName;
        }

        private void ReadDescriptionFile(string sBoxDescriptionFile)
        {
            StreamReader sr = new StreamReader(sBoxDescriptionFile);
            string sSizeLine = sr.ReadLine();
            string[] asSizeLine = sSizeLine.Split(',');
            Width = int.Parse(asSizeLine[0].Trim());
            Length = int.Parse(asSizeLine[1].Trim());
            Map = new int[Width, Length];
            Boxes = new List<Box>();
            for (int i = 0; i < Length; i++)
            {
                string sLine = sr.ReadLine();
                for (int j = 0; j < Width; j++)
                {
                    if (sLine[j] == 'X')
                        Map[j, i] = 0;
                    if (sLine[j] == '1')
                    {
                        Map[j, i] = 1;
                        Boxes.Add(new Box(j + 1, i + 1, 1, Boxes.Count));
                    }
                    if (sLine[j] == '2')
                    {
                        Map[j, i] = 2;
                        Boxes.Add(new Box(j + 1, i + 1, 2, Boxes.Count));
                    }
                    if (sLine[j] == 'A')
                    {
                        Map[j, i] = -1;
                        Agents++;
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
            sDomain += "(problem " + Name + ")\n";
            sDomain += "(:domain " + Name + ")\n";
            sDomain += "(:goal (and";
            foreach (Box b in Boxes)
            {
                sDomain += " (box-at b" + b.ID + " " + GetPosition(b.X, 1) + ")";
            }
            sDomain += "))\n";
            sDomain += GetInitState();
            sDomain += ")";
            return sDomain;
        }

        private string GetPosition(int iX, int iY)
        {
            return "p" + iX + "-" + iY;
        }
        private string GetAdjacent(int iX1, int iY1, int iX2, int iY2)
        {
            return "\t(adj " + GetPosition(iX1, iY1) + " " + GetPosition(iX2, iY2) + ")\n";
        }
        private string GetAdjacents()
        {
            string sAdjacents = "";
            for (int iX = 1; iX <= Width; iX++)
            {
                for (int iY = 1; iY <= Length; iY++)
                {
                    //sAdjacents += GetAdjacent(iX, iY, iX, iY);
                    if (iX > 1)
                        sAdjacents += GetAdjacent(iX, iY, iX - 1, iY);
                    if (iX < Width)
                        sAdjacents += GetAdjacent(iX, iY, iX + 1, iY);
                    if (iY > 1)
                        sAdjacents += GetAdjacent(iX, iY, iX, iY - 1);
                    if (iY < Length)
                        sAdjacents += GetAdjacent(iX, iY, iX, iY + 1);
                }
            }
            return sAdjacents;
        }

        private string GetInitState()
        {
            string sInit = "(:init\n";
            sInit += "\t(and\n";
            //sInit += "\t\t(eq move-n-push move-n-push)";
            //sInit += "\t\t(eq move-only move-only)";
            sInit += "\t\t(agent-at a1 " + GetPosition(Width, Length) + ")" + "\n";
            sInit += "\t\t(agent-at a2 " + GetPosition(1, Length) + ")" + "\n";
            sInit += GetAdjacents() + "\n";


            foreach (Box b in Boxes)
            {
                if (b.Weight == 1)
                    sInit += "\t\t(not (heavy b" + b.ID + "))\n";
                else
                    sInit += "\t\t(heavy b" + b.ID + ")\n";
                sInit += "\t\t(oneof (box-at b" + b.ID + " " + GetPosition(b.X, b.Y) + ") (box-at b" + b.ID + " " + GetPosition(b.X, 1) + "))\n";
            }

            sInit += "\t)\n)\n";
            return sInit;
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
            sw.Write("(:types POS AGENT BOX PUSH)\n");
            sw.Write(GenerateConstants() + "\n");
            sw.Write(GeneratePredicates());
            GenerateActions(sw);
            sw.Write(")");
        }

        private void GenerateActions(StreamWriter sw)
        {
            sw.WriteLine(GenerateMoveAction());
            sw.WriteLine(GeneratePushAction());
            sw.WriteLine(GenerateJointPushAction());
            sw.WriteLine(GenerateObserveBoxAction());
        }

        private string GenerateObserveBoxAction()
        {
            string sAction = "(:action observe-box\n";
            sAction += "\t:parameters (?i - pos ?a - agent ?b - box)\n";

            sAction += "\t:precondition (and (agent-at ?a ?i))\n";
            sAction += "\t:observe (box-at ?b ?i)\n";

            sAction += ")\n";

            return sAction;
        }


        private string GenerateMoveAction()
        {
            string sAction = "(:action move\n";
            sAction += "\t:parameters (?start - pos ?end - pos ?a - agent)\n";

            sAction += "\t:precondition (and (adj ?start ?end) (agent-at ?a ?start))\n";
            sAction += "\t:effect (and (not (agent-at ?a ?start)) (agent-at ?a ?end))\n";

            sAction += ")\n";

            return sAction;
        }

        private string GeneratePushAction()
        {
            string sAction = "(:action push\n";
            sAction += "\t:parameters (?start - pos ?end - pos ?b - box ?a - agent)\n";

            sAction += "\t:precondition (and (adj ?start ?end) (agent-at ?a ?start) (box-at ?b ?start) (not (heavy ?b)))\n";
            sAction += "\t:effect (and (not (agent-at ?a ?start)) (agent-at ?a ?end) (not (box-at ?b ?start)) (box-at ?b ?end))\n";

            sAction += ")\n";

            return sAction;
        }
        private string GenerateJointPushAction()
        {
            string sAction = "(:action joint-push\n";
            sAction += "\t:parameters (?start - pos ?end - pos ?b - box)\n";

            sAction += "\t:precondition (and (adj ?start ?end) (agent-at a1 ?start) (agent-at a2 ?start) (box-at ?b ?start))\n";
            sAction += "\t:effect (and (not (agent-at a1 ?start)) (agent-at a1 ?end) (not (agent-at a2 ?start)) (agent-at a2 ?end) (not (box-at ?b ?start)) (box-at ?b ?end))\n";

            sAction += ")\n";

            return sAction;
        }


        private string GenerateConstants()
        {
            string sConstants = "(:constants\n\t";
            for (int i = 1; i <= Width; i++)
                for (int j = 1; j <= Length; j++)
                    sConstants += " p" + i + "-" + j;
            sConstants += " - pos\n\t";
            foreach (Box b in Boxes)
                sConstants += " b" + b.ID;
            sConstants += " - box\n\t";
            sConstants += " a1 a2 - agent\n\t";
            sConstants += ")\n";
            return sConstants;
        }

        private string GeneratePredicates()
        {
            string sPredicates = "(:predicates\n";
            sPredicates += "\t(adj ?i ?j - pos)\n";
            sPredicates += "\t(agent-at ?a - agent ?i - pos)\n";
            sPredicates += "\t(box-at ?b - box ?i - pos)\n";
            sPredicates += "\t(heavy ?b - box)\n";
            //sPredicates += "\t(eq ?p1 ?p2 - push)\n";
            sPredicates += ")\n";
            return sPredicates;
        }

    }
}
