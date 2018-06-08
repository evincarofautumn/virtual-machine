using System;
using System.Linq;
using System.Collections.Generic;
using System.IO;

namespace SimpLang
{
	/*
	 * This virtual machine has two separate memory regions, both
	 * of which operate as stacks: the call stack and the value
	 * stack.  Programs have direct access to the value stack and
	 * indirect access, via `Call` and `Return`, to the call stack.
	 */

	public enum Opcode
	{
		Call,			// call REL, N, REG
		Return,			// return REG-RESULT
		Jump,			// jump REL
		JumpIfZero,		// jump-if-zero REG, REL
		Set,			// set REG, CONST
		Move,			// move REG-DST, REG-SRC
		Add,			// add REG-RESULT, REG-A, REG-B
		Multiply,		// multiply REG-RESULT, REG-A, REG-B
		LessThan,		// less-than REG-RESULT, REG-A, REG-B
		Equals,			// equals REG-RESULT, REG-A, REG-B
		Not,			// not REG-RESULT, REG
		Negate,			// negate REG-RESULT, REG
	}

	public struct Instruction
	{
		// not all of these are used for every instruction
		public Opcode Opcode;
		public int I1, I2, I3;
		public long L;
		public override string ToString() {
			return Opcode + "(I1:" + I1 + ", I2:" + I2 + ", I3:" + I3 + ", L:" + L + ")";
		}
	}

	public class RegisterMachine
	{
		static void ReadReg (ref Instruction ins, string[] args) {
			ins.I1 = Int32.Parse (args [0]);
		}

		static void ReadRegReg (ref Instruction ins, string[] args) {
			ins.I1 = Int32.Parse (args [0]);
			ins.I2 = Int32.Parse (args [1]);
		}

		static void ReadRegRegReg (ref Instruction ins, string[] args) {
			ins.I1 = Int32.Parse (args [0]);
			ins.I2 = Int32.Parse (args [1]);
			ins.I3 = Int32.Parse (args [2]);
		}

		static void ReadConst (ref Instruction ins, string[] args) {
			ins.L = Int64.Parse (args [0]);
		}

		static void ReadRegConst (ref Instruction ins, string[] args) {
			ins.I1 = Int32.Parse (args [0]);
			ins.L = Int64.Parse (args [1]);
		}

		static void ReadTargetIntReg (int pc, ref Instruction ins, string[] args) {
			ins.I1 = Int32.Parse (args [0]) - pc;
			ins.I2 = Int32.Parse (args [1]);
			ins.I3 = Int32.Parse (args [2]);
		}

		static void ReadTarget (int pc, ref Instruction ins, string[] args) {
			ins.I1 = Int32.Parse (args [0]) - pc;
		}

		static void ReadRegTarget (int pc, ref Instruction ins, string[] args) {
			ins.I1 = Int32.Parse (args [0]);
			ins.I2 = Int32.Parse (args [1]) - pc;
		}

		static void ReadRegRegTarget (int pc, ref Instruction ins, string[] args) {
			ins.I1 = Int32.Parse (args [0]);
			ins.I2 = Int32.Parse (args [1]);
			ins.I3 = Int32.Parse (args [2]) - pc;
		}

		static Instruction[] ReadProgram (StreamReader reader) {
			var opcodeValues = Enum.GetValues (typeof (Opcode));

			var program = new List<Instruction> ();
			for (;;) {
				var pc = program.Count;
				var line = reader.ReadLine ();
				if (line == null)
					break;
				var elems = line.Split (new[] {' ', '\t', ',', '$'}, StringSplitOptions.RemoveEmptyEntries);
				if (elems.Length == 0)
					break;
				var opcodeName = elems [1];
				Opcode? opcode = null;
				foreach (var ov in opcodeValues) {
					if (opcodeName == Enum.GetName (typeof(Opcode), ov)) {
						opcode = (Opcode)ov;
						break;
					}
				}
				if (opcode == null)
					throw new Exception ("Read unknown opcode");
				Instruction ins = new Instruction { Opcode = (Opcode) opcode };
				var args = elems.Skip (2).ToArray ();
				switch (ins.Opcode) {
				case Opcode.Return:
					ReadReg (ref ins, args);
					break;
				case Opcode.Call:
					ReadTargetIntReg (pc, ref ins, args);
					break;
				case Opcode.Jump:
					ReadTarget (pc, ref ins, args);
					break;
				case Opcode.JumpIfZero:
					ReadRegTarget (pc, ref ins, args);
					break;
				case Opcode.Set:
					ReadRegConst (ref ins, args);
					break;
				case Opcode.Move:
				case Opcode.Not:
				case Opcode.Negate:
					ReadRegReg (ref ins, args);
					break;
				case Opcode.Add:
				case Opcode.Multiply:
				case Opcode.LessThan:
				case Opcode.Equals:
					ReadRegRegReg (ref ins, args);
					break;
				default:
					throw new ArgumentOutOfRangeException ();
				}
				program.Add (ins);
			}
			return program.ToArray ();
		}

		static long Run (Instruction[] program, long[] arguments) {
			var cs = new int [4096];	 		// call stack
			var vs = new long [1024 * 1024];	// value stack
			var csp = 0;						// call stack pointer
			var vsp = 0;						// value stack pointer
			var pc = 0;							// program counter

			// push the arguments onto the value stack
			for (int i = 0; i < arguments.Length; ++i)
				vs [vsp++] = arguments [i];

			for (;;) {
				var ins = program [pc];
				// Console.WriteLine (ins);
				switch (ins.Opcode) {
				case Opcode.Call:
					cs [csp++] = pc;
					pc += ins.I1;
					// push the stack
					vsp += ins.I2;
					continue;
				case Opcode.Return: {
						/*
						 * `Return` executes part of the corresponding `Call`
						 * instruction, namely popping the stack and assigning
						 * the returned value to the result register.
						 */
						var result = vs [vsp + ins.I1];
						// the last return halts the program
						if (csp == 0)
							return result;
						--csp;
						// get the program counter of the `Call` instruction
						pc = cs [csp];
						// the `Call` instruction
						ins = program [pc];
						// pop the stack
						vsp -= ins.I2;
						// assign the result
						vs [vsp + ins.I3] = result;
					}
					break;
				case Opcode.Jump:
					pc += ins.I1;
					continue;
				case Opcode.JumpIfZero:
					if (vs [vsp + ins.I1] == 0L) {
						pc += ins.I2;
						continue;
					}
					break;
				case Opcode.Set:
					vs [vsp + ins.I1] = ins.L;
					break;
				case Opcode.Move:
					vs [vsp + ins.I1] = vs [vsp + ins.I2];
					break;
				case Opcode.Add:
					vs [vsp + ins.I1] = vs [vsp + ins.I2] + vs [vsp + ins.I3];
					break;
				case Opcode.Multiply:
					vs [vsp + ins.I1] = vs [vsp + ins.I2] * vs [vsp + ins.I3];
					break;
				case Opcode.LessThan:
					vs [vsp + ins.I1] = vs [vsp + ins.I2] < vs [vsp + ins.I3] ? 1L : 0L;
					break;
				case Opcode.Equals:
					vs [vsp + ins.I1] = vs [vsp + ins.I2] == vs [vsp + ins.I3] ? 1L : 0L;
					break;
				case Opcode.Not:
					vs [vsp + ins.I1] = vs [vsp + ins.I2] == 0L ? 1L : 0L;
					break;
				case Opcode.Negate:
					vs [vsp + ins.I1] = -vs [vsp + ins.I2];
					break;
				default:
					throw new ArgumentOutOfRangeException ();
				}
				++pc;
			}
		}

		public static int Main (string[] args) {
			var filename = args [0];
			var machineArgs = args.Skip (1).Select (s => Int64.Parse (s)).ToArray ();
			Instruction[] program;
			using (var reader = new StreamReader (filename)) {
				program = ReadProgram (reader);
			}
			var result = Run (program, machineArgs);
			Console.WriteLine (result);
			return 0;
		}
	}
}
