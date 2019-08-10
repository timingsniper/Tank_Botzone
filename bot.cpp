#include <stack>
#include <set>
#include <string>
#include <iostream>
#include <ctime>
#include <cstring>
#include <queue>
#include<algorithm>
#include<cmath>
#ifdef _BOTZONE_ONLINE
#include "jsoncpp/json.h"
#else
#include <json/json.h>
#endif

using std::string;
using std::cin;
using std::cout;
using std::endl;
using std::flush;
using std::getline;
using std::queue;
namespace TankGame
{
	using std::stack;
	using std::set;
	using std::istream;

#ifdef _MSC_VER
#pragma region 常量定义和说明
#endif

	enum GameResult
	{
		NotFinished = -2,
		Draw = -1,
		Blue = 0,
		Red = 1
	};

	enum FieldItem
	{
		None = 0,
		Brick = 1,
		Steel = 2,
		Base = 4,
		Blue0 = 8,
		Blue1 = 16,
		Red0 = 32,
		Red1 = 64,
		Water = 128
	};
	template<typename T> inline T operator~ (T a) { return (T)~(int)a; }
	template<typename T> inline T operator| (T a, T b) { return (T)((int)a | (int)b); }
	template<typename T> inline T operator& (T a, T b) { return (T)((int)a & (int)b); }
	template<typename T> inline T operator^ (T a, T b) { return (T)((int)a ^ (int)b); }
	template<typename T> inline T& operator|= (T& a, T b) { return (T&)((int&)a |= (int)b); }
	template<typename T> inline T& operator&= (T& a, T b) { return (T&)((int&)a &= (int)b); }
	template<typename T> inline T& operator^= (T& a, T b) { return (T&)((int&)a ^= (int)b); }

	enum Action
	{
		Invalid = -2,
		Stay = -1,
		Up, Right, Down, Left,
		UpShoot, RightShoot, DownShoot, LeftShoot
	};

	// 坐标左上角为原点（0, 0），x 轴向右延伸，y 轴向下延伸
	// Side（对战双方） - 0 为蓝，1 为红
	// Tank（每方的坦克） - 0 为 0 号坦克，1 为 1 号坦克
	// Turn（回合编号） - 从 1 开始

	const int fieldHeight = 9, fieldWidth = 9, sideCount = 2, tankPerSide = 2;

	// 基地的横坐标
	const int baseX[sideCount] = { fieldWidth / 2, fieldWidth / 2 };

	// 基地的纵坐标
	const int baseY[sideCount] = { 0, fieldHeight - 1 };

	const int dx[4] = { 0, 1, 0, -1 }, dy[4] = { -1, 0, 1, 0 };
	const FieldItem tankItemTypes[sideCount][tankPerSide] = {
			{ Blue0, Blue1 },{ Red0, Red1 }
	};

	int maxTurn = 100;
	bool shoot[tankPerSide]={true,true};

#ifdef _MSC_VER
	#pragma endregion

#pragma region 工具函数和类
#endif

	inline bool ActionIsMove(Action x)
	{
		return x >= Up && x <= Left;
	}

	inline bool ActionIsShoot(Action x)
	{
		return x >= UpShoot && x <= LeftShoot;
	}

	inline bool ActionDirectionIsOpposite(Action a, Action b)
	{
		return a >= Up && b >= Up && (a + 2) % 4 == b % 4;
	}

	inline bool CoordValid(int x, int y)
	{
		return x >= 0 && x < fieldWidth && y >= 0 && y < fieldHeight;
	}

	// 判断 item 是不是叠在一起的多个坦克
	inline bool HasMultipleTank(FieldItem item)
	{
		// 如果格子上只有一个物件，那么 item 的值是 2 的幂或 0
		// 对于数字 x，x & (x - 1) == 0 当且仅当 x 是 2 的幂或 0
		return !!(item & (item - 1));
	}

	inline int GetTankSide(FieldItem item)
	{
		return item == Blue0 || item == Blue1 ? Blue : Red;
	}

	inline int GetTankID(FieldItem item)
	{
		return item == Blue0 || item == Red0 ? 0 : 1;
	}

	// 获得动作的方向
	inline int ExtractDirectionFromAction(Action x)
	{
		if (x >= Up)
			return x % 4;
		return -1;
	}

	// 物件消失的记录，用于回退
	struct DisappearLog
	{
		FieldItem item;

		// 导致其消失的回合的编号
		int turn;

		int x, y;
		bool operator< (const DisappearLog& b) const
		{
			if (x == b.x)
			{
				if (y == b.y)
					return item < b.item;
				return y < b.y;
			}
			return x < b.x;
		}
	};

#ifdef _MSC_VER
	#pragma endregion

#pragma region TankField 主要逻辑类
#endif

	class TankField
	{
	public:
		//!//!//!// 以下变量设计为只读，不推荐进行修改 //!//!//!//

		// 游戏场地上的物件（一个格子上可能有多个坦克）
		FieldItem gameField[fieldHeight][fieldWidth] = {};

		// 坦克是否存活
		bool tankAlive[sideCount][tankPerSide] = { { true, true },{ true, true } };

		// 基地是否存活
		bool baseAlive[sideCount] = { true, true };

		// 坦克横坐标，-1表示坦克已炸
		int tankX[sideCount][tankPerSide] = {
				{ fieldWidth / 2 - 2, fieldWidth / 2 + 2 },{ fieldWidth / 2 + 2, fieldWidth / 2 - 2 }
		};

		// 坦克纵坐标，-1表示坦克已炸
		int tankY[sideCount][tankPerSide] = { { 0, 0 },{ fieldHeight - 1, fieldHeight - 1 } };

		// 当前回合编号
		int currentTurn = 1;

		// 我是哪一方
		int mySide;

		// 用于回退的log
		stack<DisappearLog> logs;

		// 过往动作（previousActions[x] 表示所有人在第 x 回合的动作，第 0 回合的动作没有意义）
		Action previousActions[101][sideCount][tankPerSide] = { { { Stay, Stay },{ Stay, Stay } } };

		//!//!//!// 以上变量设计为只读，不推荐进行修改 //!//!//!//

		// 本回合双方即将执行的动作，需要手动填入
		Action nextAction[sideCount][tankPerSide] = { { Invalid, Invalid },{ Invalid, Invalid } };

		// 判断行为是否合法（出界或移动到非空格子算作非法）
		// 未考虑坦克是否存活
		bool ActionIsValid(int side, int tank, Action act)
		{
			if (act == Invalid)
				return false;
			if (act > Left && previousActions[currentTurn - 1][side][tank] > Left) // 连续两回合射击
				return false;
			if (act == Stay || act > Left)
				return true;
			int x = tankX[side][tank] + dx[act],
					y = tankY[side][tank] + dy[act];
			return CoordValid(x, y) && gameField[y][x] == None;// water cannot be stepped on
		}

		// 判断 nextAction 中的所有行为是否都合法
		// 忽略掉未存活的坦克
		bool ActionIsValid()
		{
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
					if (tankAlive[side][tank] && !ActionIsValid(side, tank, nextAction[side][tank]))
						return false;
			return true;
		}

	private:
		void _destroyTank(int side, int tank)
		{
			tankAlive[side][tank] = false;
			tankX[side][tank] = tankY[side][tank] = -1;
		}

		void _revertTank(int side, int tank, DisappearLog& log)
		{
			int &currX = tankX[side][tank], &currY = tankY[side][tank];
			if (tankAlive[side][tank])
				gameField[currY][currX] &= ~tankItemTypes[side][tank];//原来坦克存活，那么就要取反，后与上这样就可以把坦克给消除掉
			else
				tankAlive[side][tank] = true;//原来坦克复活
			currX = log.x;//提取上次的位置
			currY = log.y;
			gameField[currY][currX] |= tankItemTypes[side][tank];//将上次位置恢复坦克
		}
	public:

		// 执行 nextAction 中指定的行为并进入下一回合，返回行为是否合法
		bool DoAction()
		{
			if (!ActionIsValid())
				return false;

			// 1 移动
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					Action act = nextAction[side][tank];

					// 保存动作
					previousActions[currentTurn][side][tank] = act;
					if (tankAlive[side][tank] && ActionIsMove(act))
					{
						int &x = tankX[side][tank], &y = tankY[side][tank];
						FieldItem &items = gameField[y][x];

						// 记录 Log
						DisappearLog log;
						log.x = x;
						log.y = y;
						log.item = tankItemTypes[side][tank];
						log.turn = currentTurn;
						logs.push(log);

						// 变更坐标
						x += dx[act];
						y += dy[act];

						// 更换标记（注意格子可能有多个坦克）
						gameField[y][x] |= log.item;
						items &= ~log.item;
					}
				}

			// 2 射♂击!
			set<DisappearLog> itemsToBeDestroyed;
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					Action act = nextAction[side][tank];
					if (tankAlive[side][tank] && ActionIsShoot(act))
					{
						int dir = ExtractDirectionFromAction(act);
						int x = tankX[side][tank], y = tankY[side][tank];
						bool hasMultipleTankWithMe = HasMultipleTank(gameField[y][x]);
						while (true)
						{
							x += dx[dir];
							y += dy[dir];
							if (!CoordValid(x, y))//发现在这个路径上没有东西，就退出
								break;
							FieldItem items = gameField[y][x];
							//tank will not be on water, and water will not be shot, so it can be handled as None
							if (items != None && items != Water)
							{
								// 对射判断
								if (items >= Blue0 &&
									!hasMultipleTankWithMe && !HasMultipleTank(items))//第一个判断表示射击的位置是有坦克的
								{
									// 自己这里和射到的目标格子都只有一个坦克
									Action theirAction = nextAction[GetTankSide(items)][GetTankID(items)];
									if (ActionIsShoot(theirAction) &&
										ActionDirectionIsOpposite(act, theirAction))//第一个条件是对方有在射击，第二个条件表示的是我的act和对方act方向的判断
									{
										// 而且我方和对方的射击方向是反的
										// 那么就忽视这次射击
										break;
									}
								}

								// 标记这些物件要被摧毁了（防止重复摧毁）
								for (int mask = 1; mask <= Red1; mask <<= 1)
									if (items & mask)
									{
										DisappearLog log;
										log.x = x;
										log.y = y;
										log.item = (FieldItem)mask;
										log.turn = currentTurn;
										itemsToBeDestroyed.insert(log);
									}
								break;
							}
						}
					}
				}

			for (auto& log : itemsToBeDestroyed)
			{
				switch (log.item)
				{
					case Base:
					{
						int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
						baseAlive[side] = false;
						break;
					}
					case Blue0:
						_destroyTank(Blue, 0);
						break;
					case Blue1:
						_destroyTank(Blue, 1);
						break;
					case Red0:
						_destroyTank(Red, 0);
						break;
					case Red1:
						_destroyTank(Red, 1);
						break;
					case Steel:
						continue;
					default:
						;
				}
				gameField[log.y][log.x] &= ~log.item;
				logs.push(log);
			}

			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
					nextAction[side][tank] = Invalid;

			currentTurn++;
			return true;
		}

		// 回到上一回合
		bool Revert()
		{
			if (currentTurn == 1)
				return false;

			currentTurn--;
			while (!logs.empty())
			{
				DisappearLog& log = logs.top();
				if (log.turn == currentTurn)
				{
					logs.pop();
					switch (log.item)
					{
						case Base:
						{
							int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
							baseAlive[side] = true;
							gameField[log.y][log.x] = Base;
							break;
						}
						case Brick:
							gameField[log.y][log.x] = Brick;
							break;
						case Blue0:
							_revertTank(Blue, 0, log);
							break;
						case Blue1:
							_revertTank(Blue, 1, log);
							break;
						case Red0:
							_revertTank(Red, 0, log);
							break;
						case Red1:
							_revertTank(Red, 1, log);
							break;
						default:
							;
					}
				}
				else
					break;
			}
			return true;
		}

		// 游戏是否结束？谁赢了？
		GameResult GetGameResult()
		{
			bool fail[sideCount] = {};
			for (int side = 0; side < sideCount; side++)
				if ((!tankAlive[side][0] && !tankAlive[side][1]) || !baseAlive[side])
					fail[side] = true;
			if (fail[0] == fail[1])
				return fail[0] || currentTurn > maxTurn ? Draw : NotFinished;
			if (fail[Blue])
				return Red;
			return Blue;
		}

		/* 三个 int 表示场地 01 矩阵（每个 int 用 27 位表示 3 行）
		   initialize gameField[][]
		   brick>water>steel
		*/
		TankField(int hasBrick[3], int hasWater[3], int hasSteel[3], int mySide) : mySide(mySide)
		{
			for (int i = 0; i < 3; i++)
			{
				int mask = 1;
				for (int y = i * 3; y < (i + 1) * 3; y++)
				{
					for (int x = 0; x < fieldWidth; x++)
					{
						if (hasBrick[i] & mask)
							gameField[y][x] = Brick;
						else if (hasWater[i] & mask)
							gameField[y][x] = Water;
						else if (hasSteel[i] & mask)
							gameField[y][x] = Steel;
						mask <<= 1;
					}
				}
			}
			for (int side = 0; side < sideCount; side++)
			{
				for (int tank = 0; tank < tankPerSide; tank++)
					gameField[tankY[side][tank]][tankX[side][tank]] = tankItemTypes[side][tank];
				gameField[baseY[side]][baseX[side]] = Base;
			}
		}
		// 打印场地
		void DebugPrint()
		{
#ifndef _BOTZONE_ONLINE
			const string side2String[] = { "蓝", "红" };
			const string boolean2String[] = { "已炸", "存活" };
			const char* boldHR = "==============================";
			const char* slimHR = "------------------------------";
			cout << boldHR << endl
				 << "图例：" << endl
				 << ". - 空\t# - 砖\t% - 钢\t* - 基地\t@ - 多个坦克" << endl
				 << "b - 蓝0\tB - 蓝1\tr - 红0\tR - 红1\tW - 水" << endl //Tank2 feature
				 << slimHR << endl;
			for (int y = 0; y < fieldHeight; y++)
			{
				for (int x = 0; x < fieldWidth; x++)
				{
					switch (gameField[y][x])
					{
						case None:
							cout << '.';
							break;
						case Brick:
							cout << '#';
							break;
						case Steel:
							cout << '%';
							break;
						case Base:
							cout << '*';
							break;
						case Blue0:
							cout << 'b';
							break;
						case Blue1:
							cout << 'B';
							break;
						case Red0:
							cout << 'r';
							break;
						case Red1:
							cout << 'R';
							break;
						case Water:
							cout << 'W';
							break;
						default:
							cout << '@';
							break;
					}
				}
				cout << endl;
			}
			cout << slimHR << endl;
			for (int side = 0; side < sideCount; side++)
			{
				cout << side2String[side] << "：基地" << boolean2String[baseAlive[side]];
				for (int tank = 0; tank < tankPerSide; tank++)
					cout << ", 坦克" << tank << boolean2String[tankAlive[side][tank]];
				cout << endl;
			}
			cout << "当前回合：" << currentTurn << "，";
			GameResult result = GetGameResult();
			if (result == -2)
				cout << "游戏尚未结束" << endl;
			else if (result == -1)
				cout << "游戏平局" << endl;
			else
				cout << side2String[result] << "方胜利" << endl;
			cout << boldHR << endl;
#endif
		}

		bool operator!= (const TankField& b) const
		{

			for (int y = 0; y < fieldHeight; y++)
				for (int x = 0; x < fieldWidth; x++)
					if (gameField[y][x] != b.gameField[y][x])
						return true;

			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					if (tankX[side][tank] != b.tankX[side][tank])
						return true;
					if (tankY[side][tank] != b.tankY[side][tank])
						return true;
					if (tankAlive[side][tank] != b.tankAlive[side][tank])
						return true;
				}

			if (baseAlive[0] != b.baseAlive[0] ||
				baseAlive[1] != b.baseAlive[1])
				return true;

			if (currentTurn != b.currentTurn)
				return true;

			return false;
		}
	};

#ifdef _MSC_VER
#pragma endregion
#endif

	TankField *field;

#ifdef _MSC_VER
#pragma region 与平台交互部分
#endif

	// 内部函数
	namespace Internals
	{
		Json::Reader reader;
#ifdef _BOTZONE_ONLINE
		Json::FastWriter writer;
#else
		Json::StyledWriter writer;
#endif

		void _processRequestOrResponse(Json::Value& value, bool isOpponent)
		{
			if (value.isArray())
			{
				if (!isOpponent)
				{
					for (int tank = 0; tank < tankPerSide; tank++)
						field->nextAction[field->mySide][tank] = (Action)value[tank].asInt();
				}
				else
				{
					for (int tank = 0; tank < tankPerSide; tank++)
						field->nextAction[1 - field->mySide][tank] = (Action)value[tank].asInt();
					field->DoAction();
				}
			}
			else
			{
				// 是第一回合，裁判在介绍场地
				int hasBrick[3], hasWater[3], hasSteel[3];
				for (int i = 0; i < 3; i++) {//Tank2 feature(???????????????)
					hasWater[i] = value["waterfield"][i].asInt();
					hasBrick[i] = value["brickfield"][i].asInt();
					hasSteel[i] = value["steelfield"][i].asInt();
				}
				field = new TankField(hasBrick, hasWater, hasSteel, value["mySide"].asInt());
			}
		}

		// 请使用 SubmitAndExit 或者 SubmitAndDontExit
		void _submitAction(Action tank0, Action tank1, string debug = "", string data = "", string globaldata = "")
		{
			Json::Value output(Json::objectValue), response(Json::arrayValue);
			response[0U] = tank0;
			response[1U] = tank1;
			output["response"] = response;
			if (!debug.empty())
				output["debug"] = debug;
			if (!data.empty())
				output["data"] = data;
			if (!globaldata.empty())
				output["globaldata"] = globaldata;
			cout << writer.write(output) << endl;
		}
	}

	// 从输入流（例如 cin 或者 fstream）读取回合信息，存入 TankField，并提取上回合存储的 data 和 globaldata
	// 本地调试的时候支持多行，但是最后一行需要以没有缩进的一个"}"或"]"结尾
	void ReadInput(istream& in, string& outData, string& outGlobalData)
	{
		Json::Value input;
		string inputString;
		do
		{
			getline(in, inputString);
		} while (inputString.empty());
#ifndef _BOTZONE_ONLINE
		// 猜测是单行还是多行
		char lastChar = inputString[inputString.size() - 1];
		if (lastChar != '}' && lastChar != ']')
		{
			// 第一行不以}或]结尾，猜测是多行
			string newString;
			do
			{
				getline(in, newString);
				inputString += newString;
			} while (newString != "}" && newString != "]");
		}
#endif
		Internals::reader.parse(inputString, input);

		if (input.isObject())
		{
			Json::Value requests = input["requests"], responses = input["responses"];
			if (!requests.isNull() && requests.isArray())
			{
				size_t i, n = requests.size();
				for (i = 0; i < n; i++)
				{
					Internals::_processRequestOrResponse(requests[i], true);
					if (i < n - 1)
						Internals::_processRequestOrResponse(responses[i], false);
				}
				outData = input["data"].asString();
				outGlobalData = input["globaldata"].asString();
				return;
			}
		}
		Internals::_processRequestOrResponse(input, true);
	}

	// 提交决策并退出，下回合时会重新运行程序
	void SubmitAndExit(Action tank0, Action tank1, string debug = "", string data = "", string globaldata = "")
	{
		Internals::_submitAction(tank0, tank1, debug, data, globaldata);
		exit(0);
	}

	// 提交决策，下回合时程序继续运行（需要在 Botzone 上提交 Bot 时选择“允许长时运行”）
	// 如果游戏结束，程序会被系统杀死
	void SubmitAndDontExit(Action tank0, Action tank1)
	{
		Internals::_submitAction(tank0, tank1);
		field->nextAction[field->mySide][0] = tank0;
		field->nextAction[field->mySide][1] = tank1;
		cout << ">>>BOTZONE_REQUEST_KEEP_RUNNING<<<" << endl;
	}
#ifdef _MSC_VER
#pragma endregion
#endif
}
int aim_x, aim_y;
int test[2][9][9]={0};
void whereigo()
{
	if (TankGame::field->mySide == 1)
	{
		aim_x = TankGame::baseX[0];
		aim_y = TankGame::baseY[0];
	}

	else
	{
		aim_x = TankGame::baseX[1];
		aim_y = TankGame::baseY[1];
	}


}
bool g(int a[9][9], int x, int y,double &count) {//f()中的那个方向上能否走出去//要确保不重复之前走过的路径
	//using namespace TankGame;
	if (x == aim_x && y == aim_y) {
		return true;
	}
	for (int i = 0; i < 4; i++) {//探索四个方向//其实只需要三个、还有一个是初始的位置
		int tx, ty;
		tx = x + TankGame::dx[i];
		ty = y + TankGame::dy[i];
		if ((tx>= 0 && tx < 9)&& (ty >= 0 && ty < 9)&&(a[ty][tx] == 0)) {//能走,把当前位置置成1
		    count++;
		    if(TankGame::field->gameField[ty][tx]==TankGame::Brick)count+=1;
			a[ty][tx] = 1;
			if ((tx >= 0 && tx < 9) && (ty >= 0 && ty < 9) && (!g(a, tx, ty,count))){
			    count--;
                if(TankGame::field->gameField[ty][tx]==TankGame::Brick)count-=1;
                a[ty][tx] = 0;//这个方向走不通 回溯
			}
			else {
				return true;
			}
		}
	}//如果有某种情况四个都不可以  那么就return false
	return false;
}
int f(int x, int y, int a[9][9]) {
	//using namespace TankGame;
	//a是个复制品，在函数内更改应该没事
	whereigo();
	a[y][x] = 1;//表示当前的位置在g()中不能重走

	double rem[4] = { -1,-1,-1,-1 }; double minvalue = 1 << 8;
	for (int i = 0; i < 4; i++)
	{//没有考虑走出地图访问Field会越界 建议使用ActionIsValid() 这个函数如果记录了previousaction还能判断有没有两次连续射击
		int value = 0;
		int tx, ty;
		tx = x + TankGame::dx[i];
		ty = y + TankGame::dy[i];
		if (!((tx >= 0 && tx < 9) && (ty >= 0 && ty < 9)))
			continue;
		if (TankGame::field->gameField[ty][tx] == TankGame::Steel || TankGame::field->gameField[ty][tx] == TankGame::Water) continue;
		else if (TankGame::field->gameField[ty][tx] == TankGame::None) value += 1;
		else if (TankGame::field->gameField[ty][tx] == TankGame::Base) value += 1;
		//else if (TankGame::field->gameField[ty][tx] == TankGame::Red1) value += 1;//如果是己方的另一辆坦克
		else value += 2;
		rem[i]=value;
		//rem[i] = value + sqrt(pow(tx - aim_x, 2) + pow(ty - aim_y, 2));//aim_x 未定义 是基地坐标 对于不同方的坦克基地坐标不同
	}
	int temp;
	for (int i = 0; i < 4; i++) {
		if (rem[i] != -1) {//这个方向能走出第一步的话
			a[y + TankGame::dy[i]][x + TankGame::dx[i]] = 1;//暂时改变一下
			if (g(a, x + TankGame::dx[i], y + TankGame::dy[i],rem[i])) {//如果可以走得通的情况下，再选择其中value最小的情况
				if (rem[i] < minvalue)minvalue = rem[i], temp = i;
			}
		}
	}
	return temp;//这里的temp在正常的有通向对面基地的路径的情况下应该是总存在的吧
}

TankGame::Action Myaction(int n) {


	//先搜索周围格子
	int x, y;

	if (TankGame::field->tankX[TankGame::field->mySide][n] == -1) return TankGame::Invalid;
	else {
		x = TankGame::field->tankX[TankGame::field->mySide][n];
		y = TankGame::field->tankY[TankGame::field->mySide][n];
		TankGame::Action myact=TankGame::Stay;
		for (int i = 0; i < 9; i++) {
			for (int j = 0; j < 9; j++) {
				switch (TankGame::field->gameField[i][j])
				{
					case 0:
					case 1:
					case 4:
					case 8:
					case 16:
					case 32:
					case 64:break;//简化field，0表示能走,1表示不能
					case 2:
					case 128:test[n][i][j] = 1; break;
					default:break;
				}
			}
		}//复制棋盘
		int temp = f(x, y, test[n]);
		//TankGame::field->tankX[TankGame::field->mySide][n]= x + TankGame::dx[temp];
		//TankGame::field->tankY[TankGame::field->mySide][n]=y + TankGame::dy[temp];//这个是最终选择的方向
		//如果直接就是地方基地的话 炮击就好
		if (TankGame::field->gameField[y + TankGame::dy[temp]][x + TankGame::dx[temp]] == TankGame::Base&&TankGame::shoot[n]) {//改 ！奇数回合开炮（不能重复开两次炮）！前面有记录回合数的变量
			switch (temp)
			{
				case 0:myact = TankGame::UpShoot; break;
				case 1:myact = TankGame::RightShoot; break;
				case 2:myact = TankGame::DownShoot; break;
				case 3:myact = TankGame::LeftShoot; break;
				default:
					break;
			}
			TankGame::shoot[n]=false;
			return myact;
		}
		//但是，在行进的时候，需要考虑很多因素
		//首先是如果在与temp相同或相反方向上有坦克的话，需要先直接先攻击
		for (int i = y, j = x; i >= 0 && i < 9 && j >= 0 && j < 9 && TankGame::shoot[n]; i += TankGame::dy[temp], j += TankGame::dx[temp]) {
			if ((TankGame::field->mySide==1)&&(TankGame::field->gameField[i][j] == 8 || TankGame::field->gameField[i][j] == 16)) {//改 炮击一次后记录action stay一回合再炮击
				//如果与temp同向有敌方坦克的话，return 炮击动作
				switch (temp)
				{
					case 0:myact = TankGame::UpShoot; break;
					case 1:myact = TankGame::RightShoot; break;
					case 2:myact = TankGame::DownShoot; break;
					case 3:myact = TankGame::LeftShoot; break;
					default:
						break;
				}
				TankGame::shoot[n]=false;
				return myact;
			}
			if ((TankGame::field->mySide == 0) && (TankGame::field->gameField[i][j] == 32 || TankGame::field->gameField[i][j] == 64)) {//改 炮击一次后记录action stay一回合再炮击
				//如果与temp同向有敌方坦克的话，return 炮击动作
				switch (temp)
				{
					case 0:myact = TankGame::UpShoot; break;
					case 1:myact = TankGame::RightShoot; break;
					case 2:myact = TankGame::DownShoot; break;
					case 3:myact = TankGame::LeftShoot; break;
					default:
						break;
				}
				TankGame::shoot[n]=false;
				return myact;
			}
			if (TankGame::field->gameField[i][j] != TankGame::None && TankGame::field->gameField[i][j] != TankGame::Water) {
				//如果路径上不是对方坦克，并且不是空或者是河的情况下，退出循环
				break;
			}
		}
		for (int i = y, j = x; i >= 0 && i < 9 && j >= 0 && j < 9&& TankGame::shoot[n]; i += TankGame::dy[(temp + 2) % 4], j += TankGame::dx[(temp + 2) % 4]) {
			if ((TankGame::field->mySide==1)&&(TankGame::field->gameField[i][j] == 8 || TankGame::field->gameField[i][j] == 16)) {//改 炮击一次后记录action stay一回合再炮击
				//如果与temp同向有敌方坦克的话，return 炮击动作
				switch ((temp+2)%4)
				{
					case 0:myact = TankGame::UpShoot; break;
					case 1:myact = TankGame::RightShoot; break;
					case 2:myact = TankGame::DownShoot; break;
					case 3:myact = TankGame::LeftShoot; break;
					default:
						break;
				}
				TankGame::shoot[n]=false;
				return myact;
			}
			if ((TankGame::field->mySide == 0) && (TankGame::field->gameField[i][j] == 32 || TankGame::field->gameField[i][j] == 64)) {//改 炮击一次后记录action stay一回合再炮击
				//如果与temp同向有敌方坦克的话，return 炮击动作
				switch ((temp+2)%4)
				{
					case 0:myact = TankGame::UpShoot; break;
					case 1:myact = TankGame::RightShoot; break;
					case 2:myact = TankGame::DownShoot; break;
					case 3:myact = TankGame::LeftShoot; break;
					default:
						break;
				}
				TankGame::shoot[n]=false;
				return myact;
			}
			if (TankGame::field->gameField[i][j] != TankGame::None && TankGame::field->gameField[i][j] != TankGame::Water) {
				//如果路径上不是对方坦克，并且不是空或者是河的情况下，退出循环
				break;
			}
		}
		//不在我方坦克行进方向的坦克则不予考虑，毕竟这辆坦克是摧毁敌方基地为主
		//其次是如果行进方向是砖，直接击碎
		if (TankGame::field->gameField[y + TankGame::dy[temp]][x + TankGame::dx[temp]] == TankGame::Brick&&TankGame::shoot[n]) {
			switch (temp)
			{
				case 0:myact = TankGame::UpShoot; break;//向下炮击
				case 1:myact = TankGame::RightShoot; break;
				case 2:myact = TankGame::DownShoot; break;
				case 3:myact = TankGame::LeftShoot; break;
				default:
					break;
			}
			TankGame::shoot[n]=false;
			return myact;
		}
		//最后如果是行进方向是空地 直接行进
		if (TankGame::field->gameField[y + TankGame::dy[temp]][x + TankGame::dx[temp]] == TankGame::None) {
			switch (temp)
			{
				case 0:myact = TankGame::Up; break;//向下炮击
				case 1:myact = TankGame::Right; break;
				case 2:myact = TankGame::Down; break;
				case 3:myact = TankGame::Left; break;
				default:
					break;
			}
			TankGame::shoot[n]=true;
			return myact;
		}
	}

}

int main()
{
	srand((unsigned)time(nullptr));
	while(true){
		string data, globaldata;
		TankGame::ReadInput(cin, data, globaldata);
		TankGame::SubmitAndExit(Myaction(0), Myaction(1));
	}
}
