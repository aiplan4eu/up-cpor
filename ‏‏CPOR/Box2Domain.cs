using System;
using System.Collections.Generic;
using System.IO;

namespace CPOR
{
    class Box2Domain
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
        public Box2Domain(string sBoxDescriptionFile)
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
                sDomain += " (box-x b" + b.ID + " v" + b.X + ")";
                sDomain += " (box-y b" + b.ID + " v1)";
            }
            sDomain += "))\n";
            sDomain += GetInitState();
            sDomain += ")";
            return sDomain;
        }

        private string GetInitState()
        {
            string sInit = "(:init\n";
            sInit += "\t(and\n";
            //sInit += "\t\t(eq move-n-push move-n-push)";
            //sInit += "\t\t(eq move-only move-only)";
            sInit += "\t\t(agent-x a1 v" + Width + ")" + "\n";
            sInit += "\t\t(agent-y a1 v" + Length + ")" + "\n";
            sInit += "\t\t(agent-x a2 v" + 1 + ")" + "\n";
            sInit += "\t\t(agent-y a2 v" + Length + ")" + "\n";


            foreach (Box b in Boxes)
            {
                if (b.Weight == 1)
                    sInit += "\t\t(not (heavy b" + b.ID + "))\n";
                else
                    sInit += "\t\t(heavy b" + b.ID + ")\n";
                sInit += "\t\t(oneof (box-y b" + b.ID + " v" + b.Y + ") (box-y b" + b.ID + " v1))\n";
                sInit += "\t\t(box-x b" + b.ID + " v" + b.X + ")\n";
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
            sw.Write("(:types VALUE AGENT BOX PUSH)\n");
            sw.Write(GenerateConstants() + "\n");
            sw.Write(GeneratePredicates());
            GenerateActions(sw);
            sw.Write(")");
        }

        private void GenerateActions(StreamWriter sw)
        {

            sw.WriteLine(GenerateMoveUp());
            sw.WriteLine(GenerateMoveDown());
            sw.WriteLine(GenerateMoveLeft());
            sw.WriteLine(GenerateMoveRight());

            sw.WriteLine(GeneratePushUp());
            sw.WriteLine(GeneratePushDown());
            sw.WriteLine(GeneratePushLeft());
            sw.WriteLine(GeneratePushRight());

            sw.WriteLine(GenerateJointPushUp());
            sw.WriteLine(GenerateJointPushDown());
            sw.WriteLine(GenerateJointPushLeft());
            sw.WriteLine(GenerateJointPushRight());

            sw.WriteLine(GenerateObserve());
        }

        private string GenerateConstants()
        {
            string sConstants = "(:constants\n\t";
            for (int j = 1; j <= Math.Max(Length, Width); j++)
                sConstants += " v" + j;
            sConstants += " - Value\n\t";
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
            sPredicates += "\t(agent-x ?a - agent ?x - Value)\n";
            sPredicates += "\t(agent-y ?a - agent ?y - Value)\n";
            sPredicates += "\t(box-x ?b - box ?x - Value)\n";
            sPredicates += "\t(box-y ?b - box ?y - Value)\n";
            sPredicates += "\t(heavy ?b - box)\n";
            //sPredicates += "\t(eq ?p1 ?p2 - push)\n";
            sPredicates += ")\n";
            return sPredicates;
        }



        private string GenerateMoveUp()
        {
            string sAction = "(:action move-up\n";
            sAction += "\t:parameters (?a - agent)\n";

            //sAction += "\t:precondition \n";
            sAction += "\t:effect (and \n";
            for (int i = 2; i <= Length; i++)
                sAction += "\t\t(when (agent-y ?a v" + i + ") (and (not (agent-y ?a v" + i + ")) (agent-y ?a v" + (i - 1) + ")))\n";
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }
        private string GenerateMoveDown()
        {
            string sAction = "(:action move-down\n";
            sAction += "\t:parameters (?a - agent)\n";

            //sAction += "\t:precondition \n";
            sAction += "\t:effect (and \n";
            for (int i = 1; i < Length; i++)
                sAction += "\t\t(when (agent-y ?a v" + i + ") (and (not (agent-y ?a v" + i + ")) (agent-y ?a v" + (i + 1) + ")))\n";
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }
        private string GenerateMoveLeft()
        {
            string sAction = "(:action move-left\n";
            sAction += "\t:parameters (?a - agent)\n";

            //sAction += "\t:precondition \n";
            sAction += "\t:effect (and \n";
            for (int i = 2; i <= Width; i++)
                sAction += "\t\t(when (agent-x ?a v" + i + ") (and (not (agent-x ?a v" + i + ")) (agent-x ?a v" + (i - 1) + ")))\n";
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }
        private string GenerateMoveRight()
        {
            string sAction = "(:action move-right\n";
            sAction += "\t:parameters (?a - agent)\n";

            //sAction += "\t:precondition \n";
            sAction += "\t:effect (and \n";
            for (int i = 1; i < Width; i++)
                sAction += "\t\t(when (agent-x ?a v" + i + ") (and (not (agent-x ?a v" + i + ")) (agent-x ?a v" + (i + 1) + ")))\n";
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }

        private string GeneratePushUp()
        {
            string sAction = "(:action push-up\n";
            sAction += "\t:parameters (?a - agent ?b - box)\n";

            sAction += "\t:precondition (not (heavy ?b))\n";
            sAction += "\t:effect (and \n";
            for (int iX = 1; iX <= Width; iX++)
            {
                for (int iY = 2; iY <= Length; iY++)
                {
                    sAction += "\t\t(when (and (agent-y ?a v" + iY + ") (box-y ?b v" + iY + ") (agent-x ?a v" + iX + ") (box-x ?b v" + iX + "))\n";
                    sAction += "\t\t\t(and (not (agent-y ?a v" + iY + ")) (agent-y ?a v" + (iY - 1) + ") (not (box-y ?b v" + iY + ")) (box-y ?b v" + (iY - 1) + ")))\n";
                }
            }
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }
        private string GeneratePushDown()
        {
            string sAction = "(:action push-down\n";
            sAction += "\t:parameters (?a - agent ?b - box)\n";

            sAction += "\t:precondition (not (heavy ?b))\n";
            sAction += "\t:effect (and \n";
            for (int iX = 1; iX <= Width; iX++)
            {
                for (int iY = 1; iY < Length; iY++)
                {
                    sAction += "\t\t(when (and (agent-y ?a v" + iY + ") (box-y ?b v" + iY + ") (agent-x ?a v" + iX + ") (box-x ?b v" + iX + "))\n";
                    sAction += "\t\t\t(and (not (agent-y ?a v" + iY + ")) (agent-y ?a v" + (iY + 1) + ") (not (box-y ?b v" + iY + ")) (box-y ?b v" + (iY + 1) + ")))\n";
                }
            }
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }
        private string GeneratePushLeft()
        {
            string sAction = "(:action push-left\n";
            sAction += "\t:parameters (?a - agent ?b - box)\n";

            sAction += "\t:precondition (not (heavy ?b))\n";
            sAction += "\t:effect (and \n";
            for (int iX = 2; iX <= Width; iX++)
            {
                for (int iY = 1; iY <= Length; iY++)
                {
                    sAction += "\t\t(when (and (agent-y ?a v" + iY + ") (box-y ?b v" + iY + ") (agent-x ?a v" + iX + ") (box-x ?b v" + iX + "))\n";
                    sAction += "\t\t\t(and (not (agent-x ?a v" + iX + ")) (agent-x ?a v" + (iX - 1) + ") (not (box-x ?b v" + iX + ")) (box-x ?b v" + (iX - 1) + ")))\n";
                }
            }
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }
        private string GeneratePushRight()
        {
            string sAction = "(:action push-right\n";
            sAction += "\t:parameters (?a - agent ?b - box)\n";

            sAction += "\t:precondition (not (heavy ?b))\n";
            sAction += "\t:effect (and \n";
            for (int iX = 1; iX < Width; iX++)
            {
                for (int iY = 1; iY <= Length; iY++)
                {
                    sAction += "\t\t(when (and (agent-y ?a v" + iY + ") (box-y ?b v" + iY + ") (agent-x ?a v" + iX + ") (box-x ?b v" + iX + "))\n";
                    sAction += "\t\t\t(and (not (agent-x ?a v" + iX + ")) (agent-x ?a v" + (iX + 1) + ") (not (box-x ?b v" + iX + ")) (box-x ?b v" + (iX + 1) + ")))\n";
                }
            }
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }

        private string GenerateJointPushUp()
        {
            string sAction = "(:action joint-push-up\n";
            sAction += "\t:parameters (?b - box)\n";

            sAction += "\t:effect (and \n";
            for (int iX = 1; iX <= Width; iX++)
            {
                for (int iY = 2; iY <= Length; iY++)
                {
                    sAction += "\t\t(when (and (agent-y a1 v" + iY + ")  (agent-y a2 v" + iY + ") (box-y ?b v" + iY + ") (agent-x a1 v" + iX + ")  (agent-x a2 v" + iX + ") (box-x ?b v" + iX + "))\n";
                    sAction += "\t\t\t(and (not (agent-y a1 v" + iY + ")) (agent-y a1 v" + (iY - 1) + ") (not (agent-y a2 v" + iY + ")) (agent-y a2 v" + (iY - 1) + ") (not (box-y ?b v" + iY + ")) (box-y ?b v" + (iY - 1) + ")))\n";
                }
            }
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }

        private string GenerateJointPushDown()
        {
            string sAction = "(:action joint-push-down\n";
            sAction += "\t:parameters (?b - box)\n";

            sAction += "\t:effect (and \n";
            for (int iX = 1; iX <= Width; iX++)
            {
                for (int iY = 1; iY < Length; iY++)
                {
                    sAction += "\t\t(when (and (agent-y a1 v" + iY + ")  (agent-y a2 v" + iY + ") (box-y ?b v" + iY + ") (agent-x a1 v" + iX + ")  (agent-x a2 v" + iX + ") (box-x ?b v" + iX + "))\n";
                    sAction += "\t\t\t(and (not (agent-y a1 v" + iY + ")) (agent-y a1 v" + (iY + 1) + ") (not (agent-y a2 v" + iY + ")) (agent-y a2 v" + (iY + 1) + ") (not (box-y ?b v" + iY + ")) (box-y ?b v" + (iY + 1) + ")))\n";
                }
            }
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }


        private string GenerateJointPushLeft()
        {
            string sAction = "(:action joint-push-left\n";
            sAction += "\t:parameters (?b - box)\n";

            sAction += "\t:effect (and \n";
            for (int iX = 2; iX <= Width; iX++)
            {
                for (int iY = 1; iY <= Length; iY++)
                {
                    sAction += "\t\t(when (and (agent-y a1 v" + iY + ")  (agent-y a2 v" + iY + ") (box-y ?b v" + iY + ") (agent-x a1 v" + iX + ")  (agent-x a2 v" + iX + ") (box-x ?b v" + iX + "))\n";
                    sAction += "\t\t\t(and (not (agent-x a1 v" + iX + ")) (agent-x a1 v" + (iX - 1) + ") (not (agent-x a2 v" + iX + ")) (agent-x a2 v" + (iX - 1) + ") (not (box-x ?b v" + iX + ")) (box-x ?b v" + (iX - 1) + ")))\n";
                }
            }
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }

        private string GenerateJointPushRight()
        {
            string sAction = "(:action joint-push-right\n";
            sAction += "\t:parameters (?b - box)\n";

            sAction += "\t:effect (and \n";
            for (int iX = 1; iX < Width; iX++)
            {
                for (int iY = 1; iY <= Length; iY++)
                {
                    sAction += "\t\t(when (and (agent-y a1 v" + iY + ")  (agent-y a2 v" + iY + ") (box-y ?b v" + iY + ") (agent-x a1 v" + iX + ")  (agent-x a2 v" + iX + ") (box-x ?b v" + iX + "))\n";
                    sAction += "\t\t\t(and (not (agent-x a1 v" + iX + ")) (agent-x a1 v" + (iX + 1) + ") (not (agent-x a2 v" + iX + ")) (agent-x a2 v" + (iX + 1) + ") (not (box-x ?b v" + iX + ")) (box-x ?b v" + (iX + 1) + ")))\n";
                }
            }
            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }



        private string GenerateObserve()
        {
            string sAction = "(:action observe-all\n";
            sAction += "\t:parameters (?a - agent ?x - Value ?y - Value)\n";

            sAction += "\t:precondition (and (agent-x ?a ?x) (agent-y ?a ?y))\n";
            sAction += "\t:observe-agent ?a (and ";
            for (int iAgent = 1; iAgent <= Agents; iAgent++)
            {
                sAction += " (agent-x a" + iAgent + " ?x)";
                sAction += " (agent-y a" + iAgent + " ?y)";
            }
            foreach (Box b in Boxes)
            {
                sAction += " (box-x b" + b.ID + " ?x)";
                sAction += " (box-y b" + b.ID + " ?y)";
            }
            sAction += ")\n";

            sAction += "\t)\n";

            sAction += ")\n";

            return sAction;
        }

    }
}
