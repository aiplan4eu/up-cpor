using System;
using System.Collections.Generic;
using System.Text;

namespace CPORLib.Parsing
{
    public class CPORStack<T>
    {
        private List<T> Items;
        public CPORStack()
        {
            Items = new List<T>();
        }
        public void Push(T item)
        {
            Items.Add(item);
        }
        public T Pop()
        {
            if (Items.Count == 0)
                return default(T);
            T t = Items[Items.Count - 1];  
            Items.RemoveAt(Items.Count - 1);
            return t;
        }
        public T Peek()
        {
            return Items[Items.Count - 1];
        }
        public int Count { get { return Items.Count; } }
    }
}
