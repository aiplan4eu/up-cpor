using System.IO;

namespace CPOR
{
    class Omelette
    {
        public int RequiredEggs { get; private set; }
        public int Bowls = 2;
        public bool WithConditions = false;
        public Omelette(int cRequiredEggs)
        {
            RequiredEggs = cRequiredEggs;
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
            sDomain += "(:goal (and (eggs-in bowl1 v" + RequiredEggs + ") (good bowl1)))\n";
            //sDomain += "(:metric minimize (cost))\n";
            sDomain += GetInitState();
            sDomain += ")";
            return sDomain;
        }

        private string GetInitState()
        {
            string sInit = "(:init\n";
            sInit += "(and\n";
            for (int i = 0; i < RequiredEggs; i++)
            {
                for (int j = 0; j < RequiredEggs; j++)
                {
                    sInit += "(plus v" + i + " v" + j + " v" + (i + j) + ")\n";
                }
            }
            for (int i = 1; i <= Bowls; i++)
            {
                sInit += "(eggs-in bowl" + i + " v0)\n";
                sInit += "(good bowl" + i + ")\n";
                for (int j = 1; j <= Bowls; j++)
                {
                    if (i != j)
                        sInit += "(different bowl" + i + " bowl" + j + ")\n";
                }

            }

            //sInit += "(= (cost) 0)\n";
            sInit += ")\n)\n";
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
            sw.Write("(:types bowl value)\n");
            sw.Write(GenerateConstants() + "\n");
            sw.Write(GeneratePredicates());
            //sw.Write(GenerateFunctions());
            GenerateActions(sw);
            sw.Write(")");
        }

        private string GenerateFunctions()
        {
            return "(:functions (cost))\n";
        }

        private void GenerateActions(StreamWriter sw)
        {
            sw.WriteLine(GenerateGetEggAction());
            if (WithConditions)
            {
                sw.WriteLine(GenerateBreakEggAction());
                sw.WriteLine(GeneratePourAction());
            }
            else
            {
                sw.WriteLine(GenerateBreakEggActionNoConditions());
                sw.WriteLine(GeneratePourActionNoConditions());
            }
            sw.WriteLine(GenerateEmptyAction());
            sw.WriteLine(GenerateObserveBowlAction());
        }
        private string GenerateObserveBowlAction()
        {
            string sAction = "(:action observe-bowl\n";
            sAction += "\t:parameters (?i - bowl)\n";
            sAction += "\t:observe (good ?i)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateGetEggAction()
        {
            string sAction = "(:action get-egg\n";
            sAction += "\t:precondition (not (holding-egg))\n";
            sAction += "\t:effect (and\n";
            sAction += "(holding-egg)\n";
            //sAction += "(oneof (good-egg) (bad-egg))\n";
            sAction += "(oneof (not (bad-egg)) (bad-egg))\n";
            sAction += "\t)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateBreakEggAction()
        {
            string sAction = "(:action break-egg\n";
            sAction += "\t:parameters (?i - bowl)\n";
            sAction += "\t:precondition (and (holding-egg))\n";
            sAction += "\t:effect (and\n";
            for (int i = 0; i < RequiredEggs; i++)
                sAction += "\t(when (eggs-in ?i v" + i + ") (and (not (eggs-in ?i v" + i + ")) (eggs-in ?i v" + (i + 1) + ")))\n";
            sAction += "(when (bad-egg) (not (good ?i)))\n";
            sAction += "(not (holding-egg))\n";
            //sAction += "(not (good-egg))\n";
            sAction += "(bad-egg)\n";
            sAction += "\t)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateBreakEggActionNoConditions()
        {
            string sAction = "(:action break-egg\n";
            sAction += "\t:parameters (?i - bowl ?v1 - value ?v2 - value)\n";
            sAction += "\t:precondition (and (holding-egg) (eggs-in ?i ?v1) (plus ?v1 v1 ?v2))\n";
            sAction += "\t:effect (and\n";
            sAction += "\t(not (eggs-in ?i ?v1)) (eggs-in ?i ?v2)\n";
            sAction += "(when (bad-egg) (not (good ?i)))\n";
            sAction += "(not (holding-egg))\n";
            //sAction += "(not (good-egg))\n";
            sAction += "(bad-egg)\n";
            sAction += "\t)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateEmptyAction()
        {
            string sAction = "(:action empty\n";
            sAction += "\t:parameters (?i - bowl)\n";
            //sAction += "\t:precondition \n";
            sAction += "\t:effect (and (good ?i)";
            for (int i = 1; i <= RequiredEggs; i++)
                sAction += " (not (eggs-in ?i v" + i + "))";
            sAction += " (eggs-in ?i v0))\n";
            sAction += ")\n";
            return sAction;
        }
        private string GeneratePourAction()
        {
            string sAction = "(:action pour\n";
            sAction += "\t:parameters (?i - bowl ?j - bowl)\n";
            sAction += "\t:precondition (different ?i ?j)\n";
            sAction += "\t:effect (and\n";
            for (int i = 1; i <= RequiredEggs; i++)
            {
                for (int j = 0; j <= RequiredEggs; j++)
                {
                    int iSum = i + j;
                    if (iSum > RequiredEggs)
                        iSum = RequiredEggs;
                    sAction += "\t(when (and (eggs-in ?i v" + i + ") (eggs-in ?j v" + j + ")) (and (not (eggs-in ?i v" + i + ")) (eggs-in ?i v0)";
                    if (iSum != j)
                        sAction += "(not (eggs-in ?j v" + j + ")) (eggs-in ?j v" + iSum + ")))\n";
                    else
                        sAction += "))\n";
                }
            }
            sAction += "(when (not (good ?i)) (not (good ?j)))\n";
            sAction += "(good ?i)\n";
            sAction += "\t)\n";
            sAction += ")\n";
            return sAction;
        }

        private string GeneratePourActionNoConditions()
        {
            string sAction = "(:action pour\n";
            sAction += "\t:parameters (?i - bowl ?j - bowl ?v1 - value ?v2 - value ?v3 - value)\n";
            sAction += "\t:precondition (and (different ?i ?j) (eggs-in ?i ?v1) (eggs-in ?j ?v2) (plus ?v1 ?v2 ?v3))\n";
            sAction += "\t:effect (and\n";
            sAction += "(not (eggs-in ?i ?v1)) (not (eggs-in ?j ?v2))\n";
            sAction += "(eggs-in ?i v0) (eggs-in ?j ?v3)\n";
            sAction += "(when (not (good ?i)) (not (good ?j)))\n";
            sAction += "(good ?i)\n";
            sAction += "\t)\n";
            sAction += ")\n";
            return sAction;
        }



        private string GenerateConstants()
        {
            string sConstants = "(:constants\n";
            for (int i = 1; i <= Bowls; i++)
                sConstants += " bowl" + i;
            sConstants += " - bowl\n";
            for (int i = 0; i <= RequiredEggs * 2; i++)
                sConstants += " v" + i;
            sConstants += " - value\n";
            sConstants += ")\n";
            return sConstants;
        }

        private string GeneratePredicates()
        {
            string sPredictes = "(:predicates\n";
            sPredictes += "\t(plus ?v1 - value ?v2 - value ?v3 - value)\n";
            sPredictes += "\t(good ?i - bowl)\n";
            sPredictes += "\t(eggs-in ?i - bowl ?j - value)\n";
            sPredictes += "\t(different ?i - bowl ?j - bowl)\n";
            sPredictes += "\t(holding-egg)\n";
            //sPredictes += "\t(good-egg)\n";
            sPredictes += "\t(bad-egg)\n";
            sPredictes += ")\n";
            return sPredictes;
        }

        public string Name { get { return "Omelette-" + RequiredEggs; } }
    }
}
