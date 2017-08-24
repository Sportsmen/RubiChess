
#include "RubiChess.h"

U64 mybitset[64];

PieceType GetPieceType(char c)
{
	switch (c)
	{
	case 'n':
	case 'N':
		return KNIGHT;
	case 'b':
	case 'B':
		return BISHOP;
	case 'r':
	case 'R':
		return ROOK;
	case 'q':
	case 'Q':
		return QUEEN;
	case 'k':
	case 'K':
		return KING;
	default:
		break;
	}
	return BLANKTYPE;
}


char PieceChar(PieceCode c)
{
	PieceType p = (PieceType)(c >> 1);
	int color = (c & 1);
	char o;
	switch (p)
	{
	case PAWN:
		o = 'p';
		break;
	case KNIGHT:
		o = 'n';
		break;
	case BISHOP:
		o = 'b';
		break;
	case ROOK:
		o = 'r';
		break;
	case QUEEN:
		o = 'q';
		break;
	case KING:
		o = 'k';
		break;
	default:
		o = ' ';
		break;
	}
	if (!color)
		o = (char)(o + ('A' - 'a'));
	return o;
}
 
chessmovestack movestack[MAXMOVELISTLENGTH];
int mstop;



chessmove::chessmove(int from, int to, PieceCode promote, PieceCode capture, int ept, int castle)
{
#ifdef BITBOARD
    code = (castle << 28) | (ept << 20) | (capture << 16) | (promote << 12) | (from << 6) | to;
#else
    int f, t;
    /* convert 0x88 coordinates to 3bit */
    f = ((from >> 1) & 0x38) | (from & 0x7);
    t = ((to >> 1) & 0x38) | (to & 0x7);
    code = (capture << 16) | (promote << 12) | (f << 6) | t;
#endif
}

chessmove::chessmove(int from, int to, PieceCode promote, PieceCode capture)
{
#ifdef BITBOARD
    code = (capture << 16) | (promote << 12) | (from << 6) | to;
#else
    int f, t;
    /* convert 0x88 coordinates to 3bit */
    f = ((from >> 1) & 0x38) | (from & 0x7);
    t = ((to >> 1) & 0x38) | (to & 0x7);
    code =  (capture << 16) | (promote << 12) | (f << 6) | t;
#endif
}

chessmove::chessmove()
{
    code = 0;
}

chessmove::chessmove(unsigned long newcode)
{
    code = newcode;
}


string chessmove::toString()
{
    char s[100];

    if (code == 0)
        return "(none)";

    int from, to;
    PieceCode promotion;
    from = GETFROM(code);
    to = GETTO(code);
    promotion = GETPROMOTION(code);

#ifdef BITBOARD
    sprintf_s(s, "%c%d%c%d%c", (from & 0x7) + 'a', ((from >> 3) & 0x7) + 1, (to & 0x7) + 'a', ((to >> 3) & 0x7) + 1, PieceChar(promotion));
#else
    sprintf_s(s, "%c%d%c%d%c", (from & 0x7) + 'a', ((from >> 4) & 0x7) + 1, (to & 0x7) + 'a', ((to >> 4) & 0x7) + 1, PieceChar(promotion));
#endif
    return s;
}

void chessmove::print()
{
    cout << toString();
}


bool chessmove::cptr(chessmove cm1, chessmove cm2)
{
	return (materialvalue[GETCAPTURE(cm1.code) >> 1] < materialvalue[GETCAPTURE(cm2.code) >> 1]);
}


chessmovelist::chessmovelist()
{
    length = 0;
}

string chessmovelist::toString()
{
	string s = "";
	for (int i = 0; i < length; i++ )
	{
        s = s + move[i].toString() + " ";
	}
	return s;
}

string chessmovelist::toStringWithValue()
{
    string s = "";
    for (int i = 0; i < length; i++)
    {
        s = s + move[i].toString() + "(" + to_string((int)move[i].value) + ") ";
    }
    return s;
}

void chessmovelist::print()
{
	printf("%s", toString().c_str());
}

void chessmovelist::resetvalue()
{
    for (int i = 0; i < length; i++)
        move[i].value = SHRT_MIN;
}

void chessmovelist::sort()
{
    chessmove temp;
    for (int i = 0; i < length; i++)
        for (int j = i+1; j < length; j++)
            if (move[j] < move[i])
            {
                temp = move[i];
                move[i] = move[j];
                move[j] = temp;
            }
}


int* chessposition::GetPositionvalueTable()
{
#ifdef BITBOARD
	int *positionvalue = new int[2 * 8 * 256 * 64];  // color piecetype phase boardindex
#else
	int *positionvalue = new int[2 * 8 * 256 * 128];  // color piecetype phase boardindex
#endif
	const int PV[][64] = {
		//PAWN
		{
			0,   0,   0,   0,   0,   0,   0,   0,
			50,  50,  50,  50,  50,  50,  50,  50,
			20,  20,  20,  20,  20,  20,  20,  20,
			0,   0,   0,   10,  10,  0,   0,   0,
			0,   -20, 10,  20,  20,  -20, -20, 0,
			0,   -10, 10,  10,  10,  -10, -10, 0,
			10,  10,  0,  -20, -20,  0,   10,  10,
			0,   0,   0,   0,   0,   0,   0,   0
		},
		{
			0,   0,   0,   0,   0,   0,   0,   0,
			100, 100, 100, 100, 100, 100, 100, 100,
			60,  60,  60,  60,  60,  60,  60,  60,
			30,  30,  30,  30,  30,  30,  30,  30,
			15,  15,  15,  15,  15,  15,  15,  15,
			5,   5,   5,   5,   5,   5,   5,   5,
			0,   0,   0,   0,   0,   0,   0,   0,
			0,   0,   0,   0,   0,   0,   0,   0
		},
		//KNIGHT
		{
			-60, -40, -20, -10, -10, -20, -40, -60,
			-40, -20, 0,   10,  10,  0,   -20, -40,
			-20, 0,   20,  30,  30,  20,  0,   -20,
			-10, 10,  30,  40,  40,  30,  10,  -10,
			-10, 10,  30,  40,  40,  30,  10,  -10,
			-20, 0,   20,  30,  30,  20,  0,   -20,
			-40, -20, 0,   10,  10,  0,   -20, -40,
			-60, -40, -20, -10, -10, -20, -40, -60
		},
		{
			-60, -40, -20, -10, -10, -20, -40, -60,
			-40, -20, 0,   10,  10,  0,   -20, -40,
			-20, 0,   20,  30,  30,  20,  0,   -20,
			-10, 10,  30,  40,  40,  30,  10,  -10,
			-10, 10,  30,  40,  40,  30,  10,  -10,
			-20, 0,   20,  30,  30,  20,  0,   -20,
			-40, -20, 0,   10,  10,  0,   -20, -40,
			-60, -40, -20, -10, -10, -20, -40, -60
		},
		//BISHOP
		{
			-60, -40, -20, -10, -10, -20, -40, -60,
			-40, -20, 0,   10,  10,  0,   -20, -40,
			-20, 0,   10,  30,  30,  10,  0,   -20,
			-10, 10,  30,  40,  40,  30,  10,  -10,
			-10, 10,  30,  40,  40,  30,  10,  -10,
			-20, 0,   10,  30,  30,  10,  0,   -20,
			-40, -20, 0,   10,  10,  0,   -20, -40,
			-60, -40, -20, -10, -10, -20, -40, -60
		},
		{
			-60, -40, -20, -10, -10, -20, -40, -60,
			-40, -20, 0,   10,  10,  0,   -20, -40,
			-20, 0,   10,  30,  30,  10,  0,   -20,
			-10, 10,  30,  40,  40,  30,  10,  -10,
			-10, 10,  30,  40,  40,  30,  10,  -10,
			-20, 0,   10,  30,  30,  10,  0,   -20,
			-40, -20, 0,   10,  10,  0,   -20, -40,
			-60, -40, -20, -10, -10, -20, -40, -60
		},
		//ROOK
		{
			-10, -10, -10, -10, -10, -10, -20, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10, -10, -10, -10, -10, -10, -20, -10
		},
		{
			-10, -10, -10, -10, -10, -10, -20, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10, -10, -10, -10, -10, -10, -20, -10
		},
		//QUEEN
		{
			-10, -10, -10, -10, -10, -10, -20, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10, -10, -10, -10, -10, -10, -20, -10
		},
		{
			-10, -10, -10, -10, -10, -10, -20, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10,  0,   0,   0,   0,   0,   0, -10,
			-10, -10, -10, -10, -10, -10, -20, -10
		},
		//KING
		{
			-30, -30, -30, -30, -30, -30, -30, -30,
			-30, -30, -30, -30, -30, -30, -30, -30,
			-30, -30, -30, -30, -30, -30, -30, -30,
			-30, -30, -30, -30, -30, -30, -30, -30,
			-30, -30, -30, -30, -30, -30, -30, -30,
			-30, -30, -30, -30, -30, -30, -30, -30,
			-30, -30, -40, -40, -40, -30, -30, -30,
			10,  10,  20,   0,   0,   0,   20,  10
		},
		{
			-30, -30, -20, -20, -20, -20, -30, -30,
			-30, -20, -20, -20, -20, -20, -20, -30,
			-20, -20, -10, -10, -10, -10, -20, -20,
			-20, -20, -10,   0,   0, -10, -20, -20,
			-20, -20, -10,   0,   0, -10, -20, -20,
			-20, -20, -10, -10, -10, -10, -20, -20,
			-30, -20, -20, -20, -20, -20, -20, -30,
			-30, -30, -20, -20, -20, -20, -30, -30
		}
	};

#ifdef BITBOARD
	for (int i = 0; i < 64; i++)
	{
		if (1)
		{
			int j1 = (i ^ 0x38);
			int j2 = i;
#else
	for (int i = 0; i < 128; i++)
	{
		if (!(i & 0x88))
		{
			int j1 = (i & 0x7) + ((7 - ((i & 0x70) >> 4)) << 3);
			int j2 = (i & 0x7) + ((i & 0x70) >> 1);
#endif
			for (int p = PAWN; p <= KING; p++)
			{
				for (int ph = 0; ph < 256; ph++)
				{
#ifdef BITBOARD
					int index1 = i | (ph << 6) | (p << 14);
					int index2 = index1 | (1 << 17);
#else
					int index1 = i | (ph << 7) | (p << 15);
					int index2 = index1 | (1 << 18);
#endif
					positionvalue[index1] = (PV[(p - 1) << 1][j1] * (255 - ph) + PV[((p - 1) << 1) | 1][j1] * ph) / 255;
					positionvalue[index2] = -(PV[(p - 1) << 1][j2] * (255 - ph) + PV[((p - 1) << 1) | 1][j2] * ph) / 255;
				}
			}
		}
	}
	return positionvalue;
}



void chessposition::mirror()
{
#ifdef BITBOARD
	int newmailbox[64];
	for (int r = 0; r < 8; r++)
	{
		for (int f = 0; f < 8; f++)
		{
			int index = (r << 3) | f;
			int mirrorindex = ((7 - r) << 3) | f;
			if (mailbox[index] != BLANK)
			{
				newmailbox[mirrorindex] = mailbox[index] ^ S2MMASK;
				BitboardClear(index, mailbox[index]);
			}
			else {
				newmailbox[mirrorindex] = BLANK;
			}
		}
	}

	for (int i = 0; i < 64; i++)
	{
		mailbox[i] = newmailbox[i];
		if (mailbox[i] != BLANK)
			BitboardSet(i, mailbox[i]);
	}

	countMaterial();

    int newstate = (state & S2MMASK) ^ S2MMASK;
	if (state & WQCMASK) newstate |= BQCMASK;
	if (state & WKCMASK) newstate |= BKCMASK;
	if (state & BQCMASK) newstate |= WQCMASK;
	if (state & BKCMASK) newstate |= WKCMASK;
	state = newstate;
	if (ept)
		ept ^= 0x38;

    int kingpostemp = kingpos[0];
	kingpos[0] = kingpos[1] ^= 0x38;
	kingpos[1] = kingpostemp ^= 0x38;

#else
	int newboard[128];
	for (int r = 0; r < 8; r++)
	{
		for (int f = 0; f < 8; f++)
		{
			int index = (r << 4) | f;
			int mirrorindex = ((7 - r) << 4) | f;
			if (board[index] != BLANK)
			{
				newboard[mirrorindex] = board[index] ^ S2MMASK;
			}
			else {
				newboard[mirrorindex] = BLANK;
			}
		}
	}

	for (int i = 0; i < 128; i++)
		board[i] = newboard[i];

	countMaterial();

	int newstate = (state & S2MMASK) ^ S2MMASK;
	if (state & WQCMASK) newstate |= BQCMASK;
	if (state & WKCMASK) newstate |= BKCMASK;
	if (state & BQCMASK) newstate |= WQCMASK;
	if (state & BKCMASK) newstate |= WKCMASK;
	state = newstate;
	if (ept)
		ept ^= 0x70;

    int kingpostemp = kingpos[0];
	kingpos[0] = kingpos[1] ^= 0x70;
	kingpos[1] = kingpostemp ^= 0x70;

#endif
}


#ifdef DEBUG
void chessposition::debug(int depth, const char* format, ...)
{
	if (depth > maxdebugdepth || depth < mindebugdepth)
		return;
	printf("!");
	for (int i = 0; i < maxdebugdepth - depth; i++)
	{
		if (depth & 1)
			printf("-");
		else
			printf("+");
	}
	va_list argptr;
	va_start(argptr, format);
	vfprintf(stdout, format, argptr);
	va_end(argptr);
}

#else
void chessposition::debug(int depth, const char* format, ...)
{
}
#endif



#ifdef BITBOARD

U64 knight_attacks[64];
U64 king_attacks[64];
U64 pawn_attacks_free[64][2];
U64 pawn_attacks_free_double[64][2];
U64 pawn_attacks_occupied[64][2];
U64 rank_attacks[64][64];
U64 file_attacks[64][64];
U64 diaga1h8_attacks[64][64];
U64 diagh1a8_attacks[64][64];
U64 epthelper[64];
U64 passedPawn[64][2];
U64 filebarrier[64][2];
U64 neighbourfiles[64];
U64 kingshield[64][2];


void initBitmaphelper()
{
    int to;
    int blocked;
    int shift;
    int delta;
    for (int from = 0; from < 64; from++)
    {
        mybitset[from] = (1ULL << from);
    }

    for (int from = 0; from < 64; from++)
    {
        //rot90[from] = (((from & 0x38) >> 3) | ((from & 0x07) << 3));

        king_attacks[from] = knight_attacks[from] = 0ULL;
        pawn_attacks_free[from][0] = pawn_attacks_occupied[from][0] = pawn_attacks_free_double[from][0] = 0ULL;
        pawn_attacks_free[from][1] = pawn_attacks_occupied[from][1] = pawn_attacks_free_double[from][1] = 0ULL;
        passedPawn[from][0] = passedPawn[from][1] = 0ULL;
        filebarrier[from][0] = filebarrier[from][1] = 0ULL;
		kingshield[from][0] = kingshield[from][1] = 0ULL;
        neighbourfiles[from] = 0ULL;

        for (int j = 0; j < 64; j++)
        {
            if (abs(FILE(from) - FILE(j)) == 1)
                neighbourfiles[from] |= BITSET(j);
        }

        for (int j = 0; j < 8; j++)
        {
            // King attacks
            to = from + orthogonalanddiagonaloffset[j];
            if (to >= 0 && to < 64 && abs(FILE(from) - FILE(to)) <= 1)
                king_attacks[from] |= BITSET(to);

            // Knight attacks
            to = from + knightoffset[j];
            if (to >= 0 && to < 64 && abs(FILE(from) - FILE(to)) <= 2)
                knight_attacks[from] |= BITSET(to);
        }

        // Pawn attacks; even for rank 0 and 7 needed for the isAttacked detection
        for (int s = 0; s < 2; s++)
        {
            pawn_attacks_free[from][s] |= BITSET(from + S2MSIGN(s) * 8);
            if (RANK(from) == 1 + 5 * s)
            {
                // Double move
                pawn_attacks_free_double[from][s] |= BITSET(from + S2MSIGN(s) * 16);
            }
            // Captures
            for (int d = -1; d <= 1; d++)
            {
                to = from + (1 - 2 * s) * 8 + d;
                if (abs(FILE(from) - FILE(to)) <= 1 && to >= 0 && to < 64)
                {
                    if (d)
                        pawn_attacks_occupied[from][s] |= BITSET(to);
                    for (int r = to; r >= 0 && r < 64; r += S2MSIGN(s) * 8)
                    {
                        passedPawn[from][s] |= BITSET(r);
                        if (!d)
                            filebarrier[from][s] |= BITSET(r);
						if (abs(RANK(from) - RANK(r)) <= 2)
							kingshield[from][s] |= BITSET(r);
					}
                }

            }
        }

        // Slider attacks
        for (int j = 0; j < 64; j++)
        {
            // rank attacks
            rank_attacks[from][j] = 0ULL;
            blocked = 0;
            for (shift = from - 1; RANK(shift) == RANK(from); shift--)
            {
                if (!blocked)
                {
                    rank_attacks[from][j] |= BITSET(shift);
                }
                blocked |= (1 << FILE(shift) & (j << 1));
            }
            blocked = 0;
            for (shift = from + 1; RANK(shift) == RANK(from); shift++)
            {
                if (!blocked)
                {
                    rank_attacks[from][j] |= BITSET(shift);
                }
                blocked |= (1 << FILE(shift) & (j << 1));
            }

            // file attacks
            file_attacks[from][j] = 0ULL;
            blocked = 0;
            for (shift = from - 8; shift >= 0; shift -= 8)
            {
                if (!blocked)
                {
                    file_attacks[from][j] |= BITSET(shift);
                }
                blocked |= (1 << RANK(shift) & (j << 1));
            }
            blocked = 0;
            for (shift = from + 8; shift < 64; shift += 8)
            {
                if (!blocked)
                {
                    file_attacks[from][j] |= BITSET(shift);
                }
                blocked |= (1 << RANK(shift) & (j << 1));
            }

            // diagonala1h8 attacks
            diaga1h8_attacks[from][j] = 0ULL;
            blocked = 0;
            delta = min(FILE(from), RANK(from));
            for (shift = from - 9; shift >= 0 && FILE(shift) != 7; shift -= 9)
            {
                if (!blocked)
                {
                    diaga1h8_attacks[from][j] |= BITSET(shift);
                }
                blocked |= (1 << (--delta) & (j << 1));
            }
            blocked = 0;
            delta = min(FILE(from), RANK(from));
            for (shift = from + 9; shift < 64 && FILE(shift) != 0; shift += 9)
            {
                if (!blocked)
                {
                    diaga1h8_attacks[from][j] |= BITSET(shift);
                }
                blocked |= (1 << (++delta) & (j << 1));
            }

            // diagonalh1a8 attacks
            diagh1a8_attacks[from][j] = 0ULL;
            blocked = 0;
            delta = min(7 - FILE(from), RANK(from));
            for (shift = from - 7; shift >= 0 && FILE(shift) != 0; shift -= 7)
            {
                if (!blocked)
                {
                    diagh1a8_attacks[from][j] |= BITSET(shift);
                }
                blocked |= (1 << (--delta) & (j << 1));
            }
            blocked = 0;
            delta = min(7 - FILE(from), RANK(from));
            for (shift = from + 7; shift < 64 && FILE(shift) != 7; shift += 7)
            {
                if (!blocked)
                {
                    diagh1a8_attacks[from][j] |= BITSET(shift);
                }
                blocked |= (1 << (++delta) & (j << 1));
            }


        }

        epthelper[from] = 0ULL;
        if (RANK(from) == 3 || RANK(from) == 4)
        {
            if (RANK(from - 1) == RANK(from))
                epthelper[from] |= BITSET(from - 1);
            if (RANK(from + 1) == RANK(from))
                epthelper[from] |= BITSET(from + 1);
        }
	}
}


chessposition::chessposition()
{
    positionvaluetable = GetPositionvalueTable();

}


chessposition::~chessposition()
{
    delete positionvaluetable;
}


bool chessposition::operator==(chessposition p)
{
    return true;
}


bool chessposition::w2m()
{
    return !(state & S2MMASK);
}


PieceType chessposition::Piece(int index)
{
    return (PieceType)(mailbox[index] >> 1);
}


void chessposition::BitboardSet(int index, PieceCode p)
{
    int s2m = p & 0x1;
    piece00[p] |= BITSET(index);
    piece90[p] |= BITSET(ROT90(index));
    piecea1h8[p] |= BITSET(ROTA1H8(index));
    pieceh1a8[p] |= BITSET(ROTH1A8(index));

    occupied00[s2m] |= BITSET(index);
    occupied90[s2m] |= BITSET(ROT90(index));
    occupieda1h8[s2m] |= BITSET(ROTA1H8(index));
    occupiedh1a8[s2m] |= BITSET(ROTH1A8(index));
}


void chessposition::BitboardClear(int index, PieceCode p)
{
	int s2m = p & 0x1;
	piece00[p] ^= BITSET(index);
	piece90[p] ^= BITSET(ROT90(index));
	piecea1h8[p] ^= BITSET(ROTA1H8(index));
	pieceh1a8[p] ^= BITSET(ROTH1A8(index));

	occupied00[s2m] ^= BITSET(index);
	occupied90[s2m] ^= BITSET(ROT90(index));
	occupieda1h8[s2m] ^= BITSET(ROTA1H8(index));
	occupiedh1a8[s2m] ^= BITSET(ROTH1A8(index));
}


void chessposition::BitboardMove(int from, int to, PieceCode p)
{
    int s2m = p & 0x1;
    piece00[p] ^= (BITSET(from) | BITSET(to));
    piece90[p] ^= (BITSET(ROT90(from)) | BITSET(ROT90(to)));
    piecea1h8[p] ^= (BITSET(ROTA1H8(from)) | BITSET(ROTA1H8(to)));
    pieceh1a8[p] ^= (BITSET(ROTH1A8(from)) | BITSET(ROTH1A8(to)));

    occupied00[s2m] ^= (BITSET(from) | BITSET(to));
    occupied90[s2m] ^= (BITSET(ROT90(from)) | BITSET(ROT90(to)));
    occupieda1h8[s2m] ^= (BITSET(ROTA1H8(from)) | BITSET(ROTA1H8(to)));
    occupiedh1a8[s2m] ^= (BITSET(ROTH1A8(from)) | BITSET(ROTH1A8(to)));
}


int chessposition::getFromFen(const char* sFen)
{
    string s;
    vector<string> token = SplitString(sFen);
    int numToken = (int)token.size();

    for (int i = 0; i < 14; i++)
        piece00[i] = piece90[i] = piecea1h8[i] = pieceh1a8[i] = 0;

    for (int i = 0; i < 64; i++)
        mailbox[i] = BLANK;

    for (int i = 0; i < 2; i++)
        occupied00[i] = occupied90[i] = occupieda1h8[i] = occupiedh1a8[i] = 0;

    // At least four token are needed (EPD style string)
    if (numToken < 4)
        return -1;

    /* the board */
    s = token[0];
    int rank = 7;
    int file = 0;
    for (unsigned int i = 0; i < s.length(); i++)
    {
        PieceCode p;
        int num = 1;
        int index = (rank << 3) | file;
        char c = s[i];
        switch (c)
        {
        case 'k':
            p = BKING;
            kingpos[1] = ((rank << 3) | file);
            break;
        case 'q':
            p = BQUEEN;
            break;
        case 'r':
            p = BROOK;
            break;
        case 'b':
            p = BBISHOP;
            break;
        case 'n':
            p = BKNIGHT;
            break;
        case 'p':
            p = BPAWN;
            break;
        case 'K':
            p = WKING;
            kingpos[0] = ((rank << 3) | file);
            break;
        case 'Q':
            p = WQUEEN;
            break;
        case 'R':
            p = WROOK;
            break;
        case 'B':
            p = WBISHOP;
            break;
        case 'N':
            p = WKNIGHT;
            break;
        case 'P':
            p = WPAWN;
            break;
        case '/':
            rank--;
            num = 0;
            file = 0;
            break;
        default:	/* digit */
            num = 0;
            file += (c - '0');
            p = BLANK;
            break;
        }
        if (num)
        {
            mailbox[index] = p;
            BitboardSet(index, p);
            file++;
        }
    }

    if (rank != 0 || file != 8)
        return -1;

    if (numToken < 0)
        return -1;

    state = 0;
    /* side to move */
    if (token[1] == "b")
        state |= S2MMASK;

    /* castle rights */
    s = token[2];
    for (unsigned int i = 0; i < s.length(); i++)
    {
        switch (s[i])
        {
        case 'Q':
            state |= WQCMASK;
            break;
        case 'K':
            state |= WKCMASK;
            break;
        case 'q':
            state |= BQCMASK;
            break;
        case 'k':
            state |= BKCMASK;
            break;
        default:
            break;
        }
    }

    /* en passant target */
    ept = 0;
    s = token[3];
    if (s.length() == 2)
    {
        int i = AlgebraicToIndex(s, 64);
        if (i < 0x88)
        {
            ept = i;
        }
    }

    /* half moves */
    if (numToken > 4)
        halfmovescounter = stoi(token[4]);

    /* full moves */
    if (numToken > 5)
        fullmovescounter = stoi(token[5]);

    actualpath.length = 0;
    countMaterial();
    hash = tp->zb.getHash(this);
    rp->clean();
    rp->addPosition(hash);
    for (int i = 0; i < 14; i++)
    {
        for (int j = 0; j < 128; j++)
        {
            history[i][j] = 0;
        }
    }
    mstop = 0;
    return 0;
}


bool chessposition::applyMove(string s)
{
    unsigned int from, to;
    bool retval = false;
    PieceCode promotion;

    from = AlgebraicToIndex(s, 64);
    to = AlgebraicToIndex(&s[2], 64);
    chessmovelist* cmlist = getMoves();
    //printf("applyMove: %s\nMovelist: %s\n", s.c_str(), cmlist.toString().c_str());
    //printf("Hash:%x   Hashmod:%x  Rep:%d\n", hash, hash % 0x10000, rp->getPositionCount(hash));
    if (s.size() > 4)
        promotion = (PieceCode)((GetPieceType(s[4]) << 1) | (state & S2MMASK));
    else
        promotion = BLANK;
    for (int i = 0; i < cmlist->length; i++)
    {
        if (GETFROM(cmlist->move[i].code) == from && GETTO(cmlist->move[i].code) == to && GETPROMOTION(cmlist->move[i].code) == promotion)
        {
            if (playMove(&(cmlist->move[i])))
            {
                retval = true;
            }
            else {
                retval = false;
            }
            break;
        }
    }
    free(cmlist);
    return retval;
}


void chessposition::print()
{
    for (int r = 7; r >= 0; r--)
    {
        printf("info string ");
        for (int f = 0; f < 8; f++)
        {
            char pc = PieceChar(mailbox[(r << 3) | f]);
            if (pc == 0)
                pc = '.';
            printf("%c", pc);
        }
        printf("\n");
    }

    printf("info string State: %0x\n", state);
    printf("info string EPT: %0x\n", ept);
    printf("info string Halfmoves: %d\n", halfmovescounter);
    printf("info string Fullmoves: %d\n", fullmovescounter);
    printf("info string Hash: %llu\n", hash);
    printf("info string Value: %d\n", getValue());
    printf("info string Repetitions: %d\n", rp->getPositionCount(hash));
    //printf("info string Possible Moves: %s\n", getMoves().toStringWithValue().c_str());
    if (tp->size > 0 && tp->testHash())
        printf("info string Hash-Info: depth=%d Val=%d (%d) Move:%s\n", tp->getDepth(), tp->getValue(), tp->getValtype(), tp->getMove().toString().c_str());
    if (actualpath.length)
        printf("info string Moves in current search: %s\n", actualpath.toString().c_str());
}


int chessposition::getValue()
{
    // Check for insufficient material using simnple heuristic from chessprogramming site
    if (!(piece00[WPAWN] | piece00[BPAWN]))
    {
        if (!(piece00[WQUEEN] | piece00[BQUEEN] | piece00[WROOK] | piece00[BROOK]))
        {
            if (POPCOUNT(piece00[WBISHOP] | piece00[WKNIGHT]) <= 2
                && POPCOUNT(piece00[BBISHOP] | piece00[BKNIGHT]) <= 2)
            {
                bool winpossible = false;
                // two bishop win if opponent has none
                if (abs(POPCOUNT(piece00[WBISHOP]) - POPCOUNT(piece00[BBISHOP])) == 2)
                    winpossible = true;
                // bishop and knight win against bare king
                if ((piece00[WBISHOP] && piece00[WKNIGHT] && !(piece00[BBISHOP] | piece00[BKNIGHT]))
                    || (piece00[BBISHOP] && piece00[BKNIGHT] && !(piece00[WBISHOP] | piece00[WKNIGHT])))
                    winpossible = true;

                if (!winpossible)
                    return SCOREDRAW;
            }
        }
    }
    return countMaterial() + getPositionValue();
}


int chessposition::getPositionValue()
{
    int index;
    int ph = phase();
    int result = 0;
    for (int s = 0; s < 2; s++)
    {
        for (int p = PAWN; p <= KING; p++)
        {
            PieceCode pc = (p << 1) | s;
            U64 pb = piece00[pc];

            while (LSB(index, pb))
            {
                int pvtindex = index | (ph << 6) | (p << 14) | (s << 17);
                result += *(positionvaluetable + pvtindex);
                pb ^= BITSET(index);
                if (p == PAWN)
                {
                    if (!(passedPawn[index][s] & piece00[pc ^ S2MMASK]))
                        // passed pawn
                        result += (S2MSIGN(s) * 40);
                    if (!(piece00[pc] & neighbourfiles[index]))
                        // isolated pawn
                        result -= S2MSIGN(s) * 20;
                    else if (POPCOUNT((piece90[pc] >> rot90shift[index]) & 0x3f) > 1)
                        // double pawn
                        result -= S2MSIGN(s) * 15;

                }
                if (shifting[p] & 0x2) // rook and queen
                {
                    if (!(filebarrier[index][s] & piece00[WPAWN | s]))
                        // free file
                        result += S2MSIGN(s) * 30;
                }

            }
        }
    }
	// some kind of king safety
	result += (255 - ph) * (POPCOUNT(piece00[WPAWN] & kingshield[kingpos[0]][0]) - POPCOUNT(piece00[BPAWN] & kingshield[kingpos[1]][1])) * 15 / 255;

    return result;
}


int chessposition::countMaterial()
{
    int value = 0;
    for (int p = PAWN; p < KING; p++)
    {
        value += (POPCOUNT(piece00[p << 1]) - POPCOUNT(piece00[(p << 1) | 1])) * materialvalue[p];
    }
	return value;
}


bool chessposition::playMove(chessmove *cm)
{
    int oldcastle = (state & CASTLEMASK);
    int s2m = state & S2MMASK;
    bool isLegal;
    int from = GETFROM(cm->code);
    int to = GETTO(cm->code);
    PieceCode pfrom = mailbox[from];
    PieceCode pto = mailbox[to];
    PieceType ptype = Piece(from);
    int eptnew = GETEPT(cm->code);
    int castle = GETCASTLE(cm->code);

    PieceCode promote = GETPROMOTION(cm->code);

    movestack[mstop].ept = ept;
    movestack[mstop].hash = hash;
    movestack[mstop].state = state;
    movestack[mstop].kingpos[0] = kingpos[0];
    movestack[mstop].kingpos[1] = kingpos[1];
    movestack[mstop].fullmovescounter = fullmovescounter;
    movestack[mstop].halfmovescounter = halfmovescounter;

    halfmovescounter++;

    // Fix hash regarding capture
    if (pto != BLANK) // use pto instead of capture here because ep capture has capture set but hits empty field here
    {
        hash ^= tp->zb.boardtable[(to << 4) | pto];
        BitboardClear(to, pto);
        halfmovescounter = 0;
    }

    if (promote == BLANK)
    {
		mailbox[to] = pfrom;
		BitboardMove(from, to, pfrom);
    }
    else {
		mailbox[to] = promote;
		BitboardClear(from, pfrom);
		BitboardSet(to, promote);
	}

    hash ^= tp->zb.boardtable[(to << 4) | mailbox[to]];
    hash ^= tp->zb.boardtable[(from << 4) | pfrom];

    mailbox[from] = BLANK;

    /* PAWN specials */
    if (ptype == PAWN)
    {
        halfmovescounter = 0;

        if (ept && to == ept)
        {
            // FIXME: to many mailbox[epfield], this is a pawn we just need to add the color
            int epfield = (from & 0x38) | (to & 0x07);
            hash ^= tp->zb.boardtable[(epfield << 4) | mailbox[epfield]];

            BitboardClear(epfield, mailbox[epfield]);
            mailbox[epfield] = BLANK;
        }
    }

	if (to == 0x00 || from == 0x00)
		state &= ~WQCMASK;
	if (to == 0x07 || from == 0x07)
		state &= ~WKCMASK;
	if (to == 0x38 || from == 0x38)
		state &= ~BQCMASK;
	if (to == 0x3f || from == 0x3f)
		state &= ~BKCMASK;

	if (ptype == KING)
    {
        kingpos[s2m] = to;
        /* handle castle */
        state &= (s2m ? ~(BQCMASK | BKCMASK) : ~(WQCMASK | WKCMASK));
        if (castle)
        {
            int rookfrom = castlerookfrom[castle];
            int rookto = castlerookto[castle];

            BitboardMove(rookfrom, rookto, (PieceCode)(WROOK | s2m));
            mailbox[rookto] = (PieceCode)(WROOK | s2m);

            hash ^= tp->zb.boardtable[(rookto << 4) | (PieceCode)(WROOK | s2m)];
            hash ^= tp->zb.boardtable[(rookfrom << 4) | (PieceCode)(WROOK | s2m)];

            mailbox[rookfrom] = BLANK;
        }
    }

    isLegal = !checkForChess();
    state ^= S2MMASK;

    hash ^= tp->zb.s2m;

    if (!(state & S2MMASK))
        fullmovescounter++;

	// Fix hash regarding ept
	hash ^= tp->zb.ept[ept];
    ept = eptnew;
	hash ^= tp->zb.ept[ept];

    // Fix hash regarding castle rights
    oldcastle ^= (state & CASTLEMASK);
	hash ^= tp->zb.cstl[oldcastle];

    ply++;
    rp->addPosition(hash);
    actualpath.move[actualpath.length++] = *cm;
    mstop++;
    if (!isLegal)
    {
        unplayMove(cm);
    }
    return isLegal;
}


void chessposition::unplayMove(chessmove *cm)
{
    int from = GETFROM(cm->code);
    int to = GETTO(cm->code);
    PieceCode pto = mailbox[to];
    int castle = GETCASTLE(cm->code);
    PieceCode promote = GETPROMOTION(cm->code);
    PieceCode capture = GETCAPTURE(cm->code);
    int s2m;

    actualpath.length--;
    rp->removePosition(hash);
    ply--;

    mstop--;
    ept = movestack[mstop].ept;
    hash = movestack[mstop].hash;
    state = movestack[mstop].state;
    kingpos[0] = movestack[mstop].kingpos[0];
    kingpos[1] = movestack[mstop].kingpos[1];
    fullmovescounter = movestack[mstop].fullmovescounter;
    halfmovescounter = movestack[mstop].halfmovescounter;

    s2m = state & S2MMASK;
    if (promote != BLANK)
    {
        mailbox[from] = (PieceCode)(WPAWN | s2m);
        BitboardClear(to, pto);
        BitboardSet(from, (PieceCode)(WPAWN | s2m));
    }
    else {
        BitboardMove(to, from, pto);
        mailbox[from] = pto;
    }

    if (capture != BLANK)
    {
        if (ept && to == ept)
        {
            // special ep capture
            int epfield = (from & 0x38) | (to & 0x07);
            BitboardSet(epfield, capture);
            mailbox[epfield] = capture;
            mailbox[to] = BLANK;
        }
        else
        {
            BitboardSet(to, capture);
            mailbox[to] = capture;
        }
    }
    else {
        mailbox[to] = BLANK;
    }

    if (castle)
    {
        int rookfrom = castlerookfrom[castle];
        int rookto = castlerookto[castle];

        BitboardMove(rookto, rookfrom, (PieceCode)(WROOK | s2m));
        mailbox[rookfrom] = (PieceCode)(WROOK | s2m);
        mailbox[rookto] = BLANK;
    }
}


bool chessposition::checkForChess()
{
    return (isAttacked(kingpos[state & S2MMASK]));
}


inline void chessposition::testMove(chessmovelist *movelist, int from, int to, PieceCode promote, PieceCode capture)
{
    chessmove cm(from, to, promote, capture);
    if (capture != BLANK)
    {
        cm.value = (mvv[capture >> 1] | lva[Piece(from)]);
    }
    else {
        cm.value = history[Piece(from)][to];
    }
    movelist->move[movelist->length++] = cm;
}


chessmovelist* chessposition::getMoves()
{
    int s2m = state & S2MMASK;
    U64 occupiedbits = (occupied00[0] | occupied00[1]);
    U64 emptybits = ~occupiedbits;
    U64 opponentorfreebits = ~occupied00[s2m];
    U64 frombits, tobits;
    int from, to;
    int mask;
    PieceCode pc;

    chessmovelist* result = (chessmovelist*)malloc(sizeof(chessmovelist));
    result->length = 0;
    for (int p = PAWN; p <= KING; p++)
    {
        pc = (PieceCode)((p << 1) | s2m);
        frombits = piece00[pc];
        switch (p)
        {
        case PAWN:
            while (LSB(from, frombits))
            {
                tobits = (pawn_attacks_free[from][s2m] & emptybits);
                if (tobits)
                    tobits |= (pawn_attacks_free_double[from][s2m] & emptybits);
                /* FIXME: ept & EPTSIDEMASK[s2m] is a quite ugly test for correct side respecting null move pruning */
                tobits |= (pawn_attacks_occupied[from][s2m] & (occupied00[s2m ^ 1] | ((ept & EPTSIDEMASK[s2m]) ? BITSET(ept) : 0ULL)));
                while (LSB(to, tobits))
                {
                    if (ept && ept == to)
                    {
                        testMove(result, from, to, BLANK, (PieceCode)(WPAWN | (s2m ^1)));
                    }
                     else if (PROMOTERANK(to))
                    {
                        testMove(result, from, to, (PieceCode)((QUEEN << 1) | s2m), mailbox[to]);
                        testMove(result, from, to, (PieceCode)((ROOK << 1) | s2m), mailbox[to]);
                        testMove(result, from, to, (PieceCode)((BISHOP << 1) | s2m), mailbox[to]);
                        testMove(result, from, to, (PieceCode)((KNIGHT << 1) | s2m), mailbox[to]);
                    }
                    else if (!((from ^ to) & 0x8) && epthelper[to] & piece00[pc ^ 1])
                    {
                        // EPT possible for opponent
                        result->move[result->length++] = chessmove(from, to, BLANK, BLANK, (from + to) >> 1, 0);
                    }
                    else {
                        testMove(result, from, to, BLANK, mailbox[to]);
                    }
                    tobits ^= BITSET(to);
                }
                frombits ^= BITSET(from);
            }
            break;
        case KNIGHT:
            while (LSB(from, frombits))
            {
                tobits = (knight_attacks[from] & opponentorfreebits);
                while (LSB(to, tobits))
                {
                    testMove(result, from, to, BLANK, mailbox[to]);
                    tobits ^= BITSET(to);
                }
                frombits ^= BITSET(from);
            }
            break;
        case KING:
            from = kingpos[s2m];
            tobits = (king_attacks[from] & opponentorfreebits);
            while (LSB(to, tobits))
            {
                testMove(result, from, to, BLANK, mailbox[to]);
                tobits ^= BITSET(to);
            }
            if (state & QCMASK[s2m])
            {
                /* queen castle */
                if (!(occupiedbits & (s2m ? 0x0e00000000000000 : 0x000000000000000e))
                    && !isAttacked(from) && !isAttacked(from - 1) && !isAttacked(from - 2))
                {
                    result->move[result->length++] = chessmove(from, from - 2, BLANK, BLANK, 0, (1 << s2m) | 1);
                }
            }
            if (state & KCMASK[s2m])
            {
                /* kink castle */
                if (!(occupiedbits & (s2m ? 0x6000000000000000 : 0x0000000000000060))
                    && !isAttacked(from) && !isAttacked(from + 1) && !isAttacked(from + 2))
                {
                    result->move[result->length++] = chessmove(from, from + 2, BLANK, BLANK, 0, (2 << s2m));
                }
            }
            break;
        default:
            tobits = 0ULL;
            while (LSB(from, frombits))
            {
                if (shifting[p] & 0x1)
                {
                    // a1h8 attacks
                    mask = (((occupieda1h8[0] | occupieda1h8[1]) >> rota1h8shift[from]) & 0x3f);
                    tobits |= (diaga1h8_attacks[from][mask] & opponentorfreebits);
                    // h1a8 attacks
                    mask = (((occupiedh1a8[0] | occupiedh1a8[1]) >> roth1a8shift[from]) & 0x3f);
                    tobits |= (diagh1a8_attacks[from][mask] & opponentorfreebits);
                }
                if (shifting[p] & 0x2)
                {
                    // rank attacks
                    mask = (((occupied00[0] | occupied00[1]) >> rot00shift[from]) & 0x3f);
                    tobits |= (rank_attacks[from][mask] & opponentorfreebits);
                    // file attacks
                    mask = (((occupied90[0] | occupied90[1]) >> rot90shift[from]) & 0x3f);
                    tobits |= (file_attacks[from][mask] & opponentorfreebits);
                }
                while (LSB(to, tobits))
                {
                    testMove(result, from, to, BLANK, mailbox[to]);
                    tobits ^= BITSET(to);
                }
                frombits ^= BITSET(from);
            }
            break;
        }
    }
    return result;
}


U64 chessposition::attacksTo(int index, int side)
{
    return (knight_attacks[index] & piece00[(KNIGHT << 1) | side])
        | (king_attacks[index] & piece00[(KING << 1) | side])
        | (pawn_attacks_occupied[index][state & S2MMASK] & piece00[(PAWN << 1) | side])
        | (rank_attacks[index][((occupied00[0] | occupied00[1]) >> ((index & 0x38) + 1)) & 0x3f] & (piece00[(ROOK << 1) | side] | piece00[(QUEEN << 1) | side]))
        | (file_attacks[index][((occupied90[0] | occupied90[1]) >> (((index & 0x07) << 3) + 1)) & 0x3f] & (piece00[(ROOK << 1) | side] | piece00[(QUEEN << 1) | side]))
        | (diaga1h8_attacks[index][((occupieda1h8[0] | occupieda1h8[1]) >> rota1h8shift[index]) & 0x3f] & (piece00[(BISHOP << 1) | side] | piece00[(QUEEN << 1) | side]))
        | (diagh1a8_attacks[index][((occupiedh1a8[0] | occupiedh1a8[1]) >> roth1a8shift[index]) & 0x3f] & (piece00[(BISHOP << 1) | side] | piece00[(QUEEN << 1) | side]));
}


bool chessposition::isAttacked(int index)
{
    int opponent = (state & S2MMASK) ^ 1;

    return knight_attacks[index] & piece00[(KNIGHT << 1) | opponent]
        || king_attacks[index] & piece00[(KING << 1) | opponent]
        || pawn_attacks_occupied[index][state & S2MMASK] & piece00[(PAWN << 1) | opponent]
        || rank_attacks[index][((occupied00[0] | occupied00[1]) >> ((index & 0x38) + 1)) & 0x3f] & (piece00[(ROOK << 1) | opponent] | piece00[(QUEEN << 1) | opponent])
        || file_attacks[index][((occupied90[0] | occupied90[1]) >> (((index & 0x07) << 3) + 1)) & 0x3f] & (piece00[(ROOK << 1) | opponent] | piece00[(QUEEN << 1) | opponent])
        || diaga1h8_attacks[index][((occupieda1h8[0] | occupieda1h8[1]) >> rota1h8shift[index]) & 0x3f] & (piece00[(BISHOP << 1) | opponent] | piece00[(QUEEN << 1) | opponent])
        || diagh1a8_attacks[index][((occupiedh1a8[0] | occupiedh1a8[1]) >> roth1a8shift[index]) & 0x3f] & (piece00[(BISHOP << 1) | opponent] | piece00[(QUEEN << 1) | opponent]);
}


int chessposition::phase()
{
    int p = max(0, (24 - POPCOUNT(piece00[4]) - POPCOUNT(piece00[5]) - POPCOUNT(piece00[6]) - POPCOUNT(piece00[7]) - (POPCOUNT(piece00[8]) << 1) - (POPCOUNT(piece00[9]) << 1) - (POPCOUNT(piece00[10]) << 2) - (POPCOUNT(piece00[11]) << 2)));
    return (p * 255 + 12) / 24;

}


int chessposition::see(int to)
{
    int cheapest = SHRT_MAX;
    int cheapest_from = -1;
    int from;
    int v;
    U64 frombits = attacksTo(to, (mailbox[to] & S2MMASK) ^ S2MMASK);
    while (LSB(from, frombits))
    {
        PieceType op = Piece(from);
        if (materialvalue[op] < cheapest)
        {
            cheapest = materialvalue[op];
            cheapest_from = from;
        }
        frombits ^= BITSET(from);
    }
    if (cheapest_from < 0)
    {
        v = 0;
    }
    else
    {
        PieceCode capture = mailbox[to];
        int material = materialvalue[Piece(to)];
        simplePlay(cheapest_from, to);
        v = max(0, material - see(to));
        simpleUnplay(cheapest_from, to, capture);
    }
    return v;
}


int chessposition::see(int from, int to)
{
    int v;
    PieceCode capture = mailbox[to];
    if (capture == BLANK)
        return 0;
    int material = materialvalue[Piece(to)];
    simplePlay(from, to);
    v = material - see(to);
    simpleUnplay(from, to, capture);
    return v;
}


void chessposition::playNullMove()
{
    state ^= S2MMASK;
    hash ^= tp->zb.s2m;
    chessmove cm;

    actualpath.move[actualpath.length++].code = 0;
}


void chessposition::unplayNullMove()
{
    state ^= S2MMASK;
    hash ^= tp->zb.s2m;
    actualpath.length--;
}


void chessposition::simplePlay(int from, int to)
{
    if (mailbox[to] != BLANK)
        BitboardClear(to, mailbox[to]);
    BitboardMove(from, to, mailbox[from]);
    mailbox[to] = mailbox[from];
    mailbox[from] = BLANK;
    state ^= S2MMASK;
}


void chessposition::simpleUnplay(int from, int to, PieceCode capture)
{
    state ^= S2MMASK;
    BitboardMove(to, from, mailbox[to]);
    mailbox[from] = mailbox[to];
    mailbox[to] = capture;
    if (capture != BLANK)
        BitboardSet(to, capture);
}


void chessposition::getpvline(int depth)
{
    int dummyval;
    chessmove cm;
    pvline.length = 0;
    while (depth >= 0)
    {
        if (pvline.length == 0 && bestmove.code > 0)
        {
            cm = bestmove;
        }
        else if (!tp->probeHash(&dummyval, &(cm.code), depth, 0, 0) || cm.code == 0)
        {
            break;
        }

        if (!playMove(&cm))
        {
            printf("Alarm. Ungültiger Zug %s in pvline\n", cm.toString().c_str());
            print();
        }
        pvline.move[pvline.length++] = cm;
        if (pvline.length == MAXMOVELISTLENGTH)
        {
            printf("Movelistalarm!!!\n");
            break;
        }
        depth--;
    }
    for (int i = pvline.length; i;)
        unplayMove(&(pvline.move[--i]));
}


/* test the actualmove for three-fold-repetition as the repetition table may give false positive due to table collisions */
bool chessposition::testRepetiton()
{
    unsigned long long h = hash;
    chessmovelist ml = actualpath;
    int hit = 0;
    int i;
    for (i = ml.length; i > 0;)
    {
        if (ml.move[--i].code == 0)
            unplayNullMove();
        else
            unplayMove(&ml.move[i]);
        if (hash == h)
            hit++;
        if (halfmovescounter == 0)
            break;
    }
    for (; i < ml.length;)
    {
        if (ml.move[i].code == 0)
        {
            playNullMove();
        }
        else
        {
            if (!playMove(&ml.move[i]))
            {
                printf("Alarm. Wie kommt ein illegaler Zug %s (%d) in die actuallist\n", ml.move[i].toString().c_str(), i);
                ml.print();
            }
        }
        i++;
    }
    if (h != hash)
    {
        printf("Alarm! testRepetitin landet bei falschem Hash-Wert.\n");
        print();
    }

    return (hit >= 2);
}


#else  // ifdef BITBOARD

chessposition::chessposition()
{
    for (int i = 0; i < 128; i++)
        board[i] = BLANK;
    positionvaluetable = GetPositionvalueTable();
}


chessposition::~chessposition()
{
    delete positionvaluetable;
}

bool chessposition::operator==(chessposition p)
{
    bool result = (state == p.state && ept == p.ept && halfmovescounter == p.halfmovescounter && value == p.value && hash == p.hash
        && kingpos[0] == p.kingpos[0] && kingpos[1] == p.kingpos[1]);
    if (result)
    {
        for (int r = 0; r < 8; r++)
        {
            for (int f = 0; f < 8; f++)
            {
                int i = ((r << 4) | f);
                result = result && (board[i] == p.board[i]);
            }
        }
        for (int i = 0; i < 7; i++)
            result = result && piecenum[i] == p.piecenum[i];
    }
    return result;
}

bool chessposition::w2m()
{
    return !(state & S2MMASK);
}



int chessposition::getFromFen(const char* sFen)
{
    string s;
    vector<string> token = SplitString(sFen);
    int numToken = (int)token.size();

    // At least four token are needed (EPD style string)
    if (numToken < 4)
        return -1;

    /* the board */
    s = token[0];
    int rank = 7;
    int file = 0;
    for (unsigned int i = 0; i < s.length(); i++)
    {
        int bIndex = (rank << 4) | file;
        char c = s[i];
        switch (c)
        {
        case 'k':
            board[bIndex] = BKING;
            kingpos[1] = bIndex;
            file++;
            break;
        case 'q':
            board[bIndex] = BQUEEN;
            file++;
            break;
        case 'r':
            board[bIndex] = BROOK;
            file++;
            break;
        case 'b':
            board[bIndex] = BBISHOP;
            file++;
            break;
        case 'n':
            board[bIndex] = BKNIGHT;
            file++;
            break;
        case 'p':
            board[bIndex] = BPAWN;
            file++;
            break;
        case 'K':
            board[bIndex] = WKING;
            kingpos[0] = bIndex;
            file++;
            break;
        case 'Q':
            board[bIndex] = WQUEEN;
            file++;
            break;
        case 'R':
            board[bIndex] = WROOK;
            file++;
            break;
        case 'B':
            board[bIndex] = WBISHOP;
            file++;
            break;
        case 'N':
            board[bIndex] = WKNIGHT;
            file++;
            break;
        case 'P':
            board[bIndex] = WPAWN;
            file++;
            break;
        case '/':
            rank--;
            file = 0;
            break;
        default:	/* digit */
            for (int i = 0; i < (c - '0'); i++)
            {
                board[bIndex++] = BLANK;
                file++;
            }
            break;
        }
    }

    if (rank != 0 || file != 8)
        return -1;

    if (numToken < 0)
        return -1;

    state = 0;
    /* side to move */
    if (token[1] == "b")
        state |= S2MMASK;

    /* castle rights */
    s = token[2];
    for (unsigned int i = 0; i < s.length(); i++)
    {
        switch (s[i])
        {
        case 'Q':
            state |= WQCMASK;
            break;
        case 'K':
            state |= WKCMASK;
            break;
        case 'q':
            state |= BQCMASK;
            break;
        case 'k':
            state |= BKCMASK;
            break;
        default:
            break;
        }
    }

    /* en passant target */
    ept = 0;
    s = token[3];
    if (s.length() == 2)
    {
        int i = AlgebraicToIndex(s, 0x88);
        if (i < 0x88)
            ept = i;
    }

    /* half moves */
    if (numToken > 4)
        halfmovescounter = stoi(token[4]);

    /* full moves */
    if (numToken > 5)
        fullmovescounter = stoi(token[5]);

    actualpath.length = 0;
    countMaterial();
    hash = tp->zb.getHash(this);
    rp->clean();
    rp->addPosition(hash);
    for (int i = 0; i < 14; i++)
    {
        for (int j = 0; j < 128; j++)
        {
            history[i][j] = 0;
        }
    }
    mstop = 0;
    return 0;
}

bool chessposition::applyMove(string s)
{
    unsigned int from, to;
    bool retval = false;
    PieceCode promotion;

	from = AlgebraicToIndex(s, 0x88);
	to = AlgebraicToIndex(&s[2], 0x88);
    chessmovelist* cmlist = getMoves();
    if (s.size() > 4)
        promotion = (PieceCode)((GetPieceType(s[4]) << 1) | (state & S2MMASK));
    else
        promotion = BLANK;
    for (int i = 0; i < cmlist->length; i++)
    {
        if (GETFROM(cmlist->move[i].code) == from && GETTO(cmlist->move[i].code) == to && GETPROMOTION(cmlist->move[i].code) == promotion)
        {
            if (playMove(&(cmlist->move[i])))
            {
                retval = true;
            }
            else {
                retval = false;
            }
            break;
        }
    }
    free(cmlist);
    return retval;
}

void chessposition::print()
{
    for (int r = 7; r >= 0; r--)
    {
        printf("info string ");
        for (int f = 0; f < 8; f++)
        {
            char pc = PieceChar(board[(r << 4) | f]);
            if (pc == 0)
                pc = '.';
            printf("%c", pc);
        }
        printf("\n");
    }

    printf("info string State: %0x\n", state);
    printf("info string EPT: %0x\n", ept);
    printf("info string Halfmoves: %d\n", halfmovescounter);
    printf("info string Fullmoves: %d\n", fullmovescounter);
    printf("info string Hash: %llu\n", hash);
    printf("info string Value: %d\n", getValue());
    printf("info string Repetitions: %d\n", rp->getPositionCount(hash));
    //printf("info string Possible Moves: %s\n", getMoves().toStringWithValue().c_str());
    if (tp->size > 0 && tp->testHash())
        printf("info string Hash-Info: depth=%d Val=%d (%d) Move:%s\n", tp->getDepth(), tp->getValue(), tp->getValtype(), tp->getMove().toString().c_str());
    if (actualpath.length)
        printf("info string Moves in current search: %s\n", actualpath.toString().c_str());
}

bool chessposition::isOnBoard(int bIndex)
{
    return !(bIndex & 0x88);
}

bool chessposition::isEmpty(int bIndex)
{
    return (!(bIndex & 0x88) && board[bIndex] == BLANK);
}

PieceType chessposition::Piece(int index)
{
    return (PieceType)(board[index] >> 1);
}

bool chessposition::isOpponent(int bIndex)
{
    return (!(bIndex & 0x88) && board[bIndex] != BLANK && ((board[bIndex] ^ state) & S2MMASK));
}

bool chessposition::isEmptyOrOpponent(int bIndex)
{
    return (!(bIndex & 0x88) && (board[bIndex] == BLANK || ((board[bIndex] ^ state) & S2MMASK)));
}

bool chessposition::isAttacked(int bIndex)
{
    int i;
    int bSource;
    int nextto;

    // check for knight attacks
    for (i = 0; i < 8; i++)
    {
        bSource = bIndex + knightoffset[i];
        if (Piece(bSource) == KNIGHT && isOpponent(bSource))
            return true;
    }

    // check for diagonal attacks
    for (i = 0; i < 4; i++)
    {
        bSource = bIndex;
        nextto = 1;
        do
        {
            bSource += diagonaloffset[i];
            if (isOpponent(bSource))
            {
                PieceType op = Piece(bSource);
                if (op == BISHOP || op == QUEEN || (op == KING && nextto) || (op == PAWN && nextto && ((state & S2MMASK) ? (diagonaloffset[i] < 0) : (diagonaloffset[i] > 0))))
                    return true;
            }
            nextto = 0;
        } while (isEmpty(bSource));
    }

    // check for ortogonal attacks
    for (i = 0; i < 4; i++)
    {
        bSource = bIndex;
        nextto = 1;
        do
        {
            bSource += orthogonaloffset[i];
            if (isOpponent(bSource))
            {
                PieceType op = Piece(bSource);
                if (op == ROOK || op == QUEEN || (op == KING && nextto))
                    return true;
            }
            nextto = 0;
        } while (isEmpty(bSource));
    }
    return false;
}


bool chessposition::checkForChess()
{
    return (isAttacked(kingpos[state & S2MMASK]));
}

void chessposition::testMove(chessmovelist *movelist, int from, int to, PieceCode promote)
{
    PieceCode capture = (!ept || to != ept || Piece(from) != PAWN ? board[to] : (PieceCode)(WPAWN | (~state & S2MMASK)));
    chessmove cm(from, to, promote, capture);
    if (true || !checkForChess())
    {
        if (capture != BLANK)
        {
            cm.value = (mvv[capture >> 1] | lva[Piece(from)]);
        }
        else {
            cm.value = history[Piece(from)][to];
        }
        movelist->move[movelist->length++] = cm;
    }
}


chessmovelist* chessposition::getMoves()
{
    int targetIndex;
    int s2m = state & S2MMASK;
    chessmovelist* result = (chessmovelist*)malloc(sizeof(chessmovelist));
    result->length = 0;

    for (int r = 0; r < 8; r++)
    {
        for (int f = 0; f < 8; f++)
        {
            int bIndex = (r << 4) | f;

            PieceCode pc = board[bIndex];
            PieceType pt = (PieceType)(pc >> 1);
            if (!((pc & S2MMASK) ^ s2m) && pt != BLANKTYPE) /* piece of side to move */
            {
                switch (pt)
                {
                case PAWN:
                    for (int i = 0; i < 3; i++)
                    {
                        targetIndex = bIndex + (s2m ? -pawnmove[i].offset : pawnmove[i].offset);
                        if (isOnBoard(targetIndex))
                        {
                            if (pawnmove[i].needsblank ? isEmpty(targetIndex) : (isOpponent(targetIndex) || (ept && ept == targetIndex)))
                            {
                                if (r == (s2m ? 1 : 6))
                                {
                                    testMove(result, bIndex, targetIndex, (PieceCode)((QUEEN << 1) | s2m));
                                    testMove(result, bIndex, targetIndex, (PieceCode)((ROOK << 1) | s2m));
                                    testMove(result, bIndex, targetIndex, (PieceCode)((BISHOP << 1) | s2m));
                                    testMove(result, bIndex, targetIndex, (PieceCode)((KNIGHT << 1) | s2m));
                                }
                                else
                                {
                                    testMove(result, bIndex, targetIndex, BLANK);

                                    if (r == (s2m ? 6 : 1) && pawnmove[i].needsblank)
                                    {
                                        int targetIndex2 = bIndex + (s2m ? -0x20 : 0x20);
                                        if (isEmpty(targetIndex2))
                                        {
                                            testMove(result, bIndex, targetIndex2, BLANK);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    break;
                case KNIGHT:
                    for (int o = 0; o < 8; o++)
                    {
                        targetIndex = bIndex + knightoffset[o];
                        if (isEmptyOrOpponent(targetIndex))
                        {
                            testMove(result, bIndex, targetIndex, BLANK);
                        }
                    }
                    break;
                case BISHOP:
                    for (int i = 0; i < 4; i++)
                    {
                        targetIndex = bIndex;
                        do
                        {
                            targetIndex += diagonaloffset[i];
                            if (isEmptyOrOpponent(targetIndex))
                            {
                                testMove(result, bIndex, targetIndex, BLANK);
                            }
                        } while (isEmpty(targetIndex));
                    }
                    break;
                case ROOK:
                    for (int i = 0; i < 4; i++)
                    {
                        targetIndex = bIndex;
                        do
                        {
                            targetIndex += orthogonaloffset[i];
                            if (isEmptyOrOpponent(targetIndex))
                            {
                                testMove(result, bIndex, targetIndex, BLANK);
                            }
                        } while (isEmpty(targetIndex));
                    }
                    break;
                case QUEEN:
                    for (int i = 0; i < 8; i++)
                    {
                        targetIndex = bIndex;
                        do
                        {
                            targetIndex += orthogonalanddiagonaloffset[i];
                            if (isEmptyOrOpponent(targetIndex))
                            {
                                testMove(result, bIndex, targetIndex, BLANK);
                            }
                        } while (isEmpty(targetIndex));
                    }
                    break;
                case KING:
                    for (int i = 0; i < 8; i++)
                    {
                        targetIndex = bIndex + orthogonalanddiagonaloffset[i];
                        if (isEmptyOrOpponent(targetIndex))
                        {
                            testMove(result, bIndex, targetIndex, BLANK);
                        }
                    }
                    if (state & (s2m ? BQCMASK : WQCMASK))
                    {
                        /* queen castle */
                        if (isEmpty(bIndex - 1) && isEmpty(bIndex - 2) && isEmpty(bIndex - 3)
                            && !isAttacked(bIndex) && !isAttacked(bIndex - 1) && !isAttacked(bIndex - 2))
                        {
                            result->move[result->length++] = chessmove(bIndex, bIndex - 2, BLANK, BLANK);
                        }
                    }
                    if (state & (s2m ? BKCMASK : WKCMASK))
                    {
                        /* kink castle */
                        if (isEmpty(bIndex + 1) && isEmpty(bIndex + 2)
                            && !isAttacked(bIndex) && !isAttacked(bIndex + 1) && !isAttacked(bIndex + 2))
                        {
                            result->move[result->length++] = chessmove(bIndex, bIndex + 2, BLANK, BLANK);
                        }
                    }
                    break;
                default:
                    break;
                }
            }
        }
    }
    return result;
}


void chessposition::simplePlay(int from, int to)
{
    board[to] = board[from];
    board[from] = BLANK;
}

void chessposition::simpleUnplay(int from, int to, PieceCode capture)
{
    board[from] = board[to];
    board[to] = capture;
}


bool chessposition::playMove(chessmove *cm)
{
    movestack[mstop].ept = ept;
    movestack[mstop].value = value;
    movestack[mstop].hash = hash;
    movestack[mstop].state = state;
    movestack[mstop].kingpos[0] = kingpos[0];
    movestack[mstop].kingpos[1] = kingpos[1];
    movestack[mstop].fullmovescounter = fullmovescounter;
    movestack[mstop].halfmovescounter = halfmovescounter;
    movestack[mstop].numFieldchanges = 0;
    int from = GETFROM(cm->code);
    int to = GETTO(cm->code);
    PieceCode promote = GETPROMOTION(cm->code);
    int eptnew = 0;
    PieceType pt = Piece(from);
    int oldcastle = (state & CASTLEMASK);
    bool isLegal;
    halfmovescounter++;

    if (promote != BLANK)
    {
        int valdiff = -materialvalue[PAWN] + materialvalue[promote >> 1];
        value += (state & S2MMASK ? -valdiff : valdiff);
        piecenum[board[from]]--;
        piecenum[promote]++;
    }
    if (Piece(to) != BLANKTYPE)
    {
        int valdiff = materialvalue[Piece(to)];
        value += (state & S2MMASK ? -valdiff : valdiff);
        piecenum[board[to]]--;
        halfmovescounter = 0;
        hash ^= tp->zb.boardtable[(to << 4) | board[to]];
    }
    
    movestack[mstop].index[movestack[mstop].numFieldchanges] = to;
    movestack[mstop].code[movestack[mstop].numFieldchanges++] = board[to];
    board[to] = (promote == BLANK ? board[from] : promote);

    // Fix hash regarding to
    hash ^= tp->zb.boardtable[(to << 4) | board[to]];
    // Fix hash regarding from
    hash ^= tp->zb.boardtable[(from << 4) | board[from]];

    movestack[mstop].index[movestack[mstop].numFieldchanges] = from;
    movestack[mstop].code[movestack[mstop].numFieldchanges++] = board[from];
    board[from] = BLANK;
    /* PAWN specials */
    if (pt == PAWN)
    {
        halfmovescounter = 0;
        /* doublemove*/
        if (!((from & 0x10) ^ (to & 0x10)))
        {
            if (board[to + 1] == (board[to] ^ S2MMASK) || board[to - 1] == (board[to] ^ S2MMASK))
                /* en passant */
                eptnew = (from + to) >> 1;
        }
        else if (ept && to == ept)
        {
            int epfield = (from & 0x70) | (to & 0x07);
            value += (state & S2MMASK ? -materialvalue[PAWN] : materialvalue[PAWN]);
            //piecenum[PAWN]--;
            piecenum[board[epfield]]--;
            // Fix hash regarding ep capture
            hash ^= tp->zb.boardtable[(epfield << 4) | board[epfield]];

            movestack[mstop].index[movestack[mstop].numFieldchanges] = epfield;
            movestack[mstop].code[movestack[mstop].numFieldchanges++] = board[epfield];
            board[epfield] = BLANK;
        }
    }
    if (to == 0x00 || from == 0x00)
        state &= ~WQCMASK;
    if (to == 0x07 || from == 0x07)
        state &= ~WKCMASK;
    if (to == 0x70 || from == 0x70)
        state &= ~BQCMASK;
    if (to == 0x77 || from == 0x77)
        state &= ~BKCMASK;

    if (pt == KING)
    {
        kingpos[state & S2MMASK] = to;
        /* handle castle */
        state &= ((state & S2MMASK) ? ~(BQCMASK | BKCMASK) : ~(WQCMASK | WKCMASK));
        if (((from & 0x3) ^ (to & 0x3)) == 0x2)
        {
            int rookfrom, rookto;
            if (to & 0x04)
            {
                /* king castle */
                rookfrom = to | 0x01;
                rookto = from | 0x01;
            }
            else {
                /* queen castle */
                rookfrom = from & 0x70;
                rookto = to | 0x01;
            }

            movestack[mstop].index[movestack[mstop].numFieldchanges] = rookto;
            movestack[mstop].code[movestack[mstop].numFieldchanges++] = board[rookto];
            board[rookto] = board[rookfrom];

            // Fix hash regarding rooks to
            hash ^= tp->zb.boardtable[(rookto << 4) | board[rookto]];
            // Fix hash regarding from
            hash ^= tp->zb.boardtable[(rookfrom << 4) | board[rookfrom]];

            movestack[mstop].index[movestack[mstop].numFieldchanges] = rookfrom;
            movestack[mstop].code[movestack[mstop].numFieldchanges++] = board[rookfrom];
            board[rookfrom] = BLANK;
        }
    }

    isLegal = !checkForChess();
    state ^= S2MMASK;

    // Fix hash regarding s2m
    hash ^= tp->zb.s2m;

	if (!(state & S2MMASK))
		fullmovescounter++;

    // Fix hash regarding old ep field
    if (ept)
        hash ^= tp->zb.ep[ept & 0x7];

    ept = eptnew;

    // Fix hash regarding new ep field
    if (ept)
        hash ^= tp->zb.ep[ept & 0x7];

    // Fix hash regarding castle rights
    oldcastle ^= (state & CASTLEMASK);
    for (int i = 0; i < 4; i++)
    {
        oldcastle >>= 1;
        if (oldcastle & 1)
            hash ^= tp->zb.castle[i];
    }

    ply++;
    rp->addPosition(hash);
    actualpath.move[actualpath.length++] = *cm;
    mstop++;
    if (!isLegal)
        unplayMove(cm);
    return isLegal;
}


void chessposition::unplayMove(chessmove *cm)
{
    actualpath.length--;
    rp->removePosition(hash);
    ply--;

    mstop--;
    ept = movestack[mstop].ept;
    value = movestack[mstop].value;
    hash = movestack[mstop].hash;
    state = movestack[mstop].state;
    kingpos[0] = movestack[mstop].kingpos[0];
    kingpos[1] = movestack[mstop].kingpos[1];
    fullmovescounter = movestack[mstop].fullmovescounter;
    halfmovescounter = movestack[mstop].halfmovescounter;
    for (int i = 0; i < movestack[mstop].numFieldchanges; i++)
    {
        if (board[movestack[mstop].index[i]] != BLANK)
            piecenum[board[movestack[mstop].index[i]]]--;
        if (movestack[mstop].code[i] != BLANK)
            piecenum[movestack[mstop].code[i]]++;
        board[movestack[mstop].index[i]] = movestack[mstop].code[i];
    }
}


void chessposition::playNullMove()
{
    state ^= S2MMASK;

    // Fix hash regarding s2m
    hash ^= tp->zb.s2m;
    chessmove cm;

    actualpath.move[actualpath.length++] = cm;
}

void chessposition::unplayNullMove()
{
    state ^= S2MMASK;

    // Fix hash regarding s2m
    hash ^= tp->zb.s2m;
    actualpath.length--;
}


void chessposition::getpvline(int depth)
{
    int dummyval;
    chessmove cm;
    pvline.length = 0;
    while (depth >= 0)
    {
        if (pvline.length == 0 && bestmove.code > 0)
        {
            cm = bestmove;
        }
        else if (!tp->probeHash(&dummyval, &(cm.code), depth, 0, 0) || cm.code == 0)
        {
            break;
        }

        if (!playMove(&cm))
        {
            printf("Alarm. Ungültiger Zug %s in pvline\n", cm.toString().c_str());
        }
        pvline.move[pvline.length++] = cm;
        if (pvline.length == MAXMOVELISTLENGTH)
        {
            printf("Movelistalarm!!!\n");
            break;
        }
        depth--;
    }
    for (int i = pvline.length; i;)
        unplayMove(&(pvline.move[--i]));
}


void chessposition::countMaterial()
{
    value = 0;
    //totalmaterial[0] = totalmaterial[1] = 0;
    for (int i = 0; i < 14; i++)
        piecenum[i] = 0;
    for (int r = 0; r < 8; r++)
    {
        for (int f = 0; f < 8; f++)
        {
            PieceCode pc = board[(r << 4) | f];
            if (pc != BLANK)
            {
                int col = pc & S2MMASK;
                piecenum[pc]++;
                value += (col ? -materialvalue[pc >> 1] : materialvalue[pc >> 1]);
            }
        }
    }
}


int chessposition::phase()
{
    //return ((24 - piecenum[2] - piecenum[3] - (piecenum[4] << 1) - (piecenum[5] << 2)) * 255 + 12) / 24;
    return (max(0, (24 - piecenum[4] - piecenum[5] - piecenum[6] - piecenum[7] - (piecenum[8] << 1) - (piecenum[9] << 1) - (piecenum[10] << 2) - (piecenum[11] << 2))) * 255 + 12) / 24;
}


int chessposition::see(int to)
{
    int i;
    int cheapest = SHRT_MAX;
    int cheapest_from = 0x88;
    int from;
    bool nextto;
    int v;

    state ^= S2MMASK;
    for (i = 0; i < 8; i++)
    {
        from = to + knightoffset[i];
        if (isOpponent(from) && (Piece(from) == KNIGHT))
        {
            cheapest_from = from;
            cheapest = materialvalue[KNIGHT];
            break;
        }
    }

    for (i = 0; i < 4; i++)
    {
        from = to;
        nextto = true;
        do
        {
            from += diagonaloffset[i];
            if (isOpponent(from))
            {
                PieceType op = Piece(from);
                if (materialvalue[op] < cheapest)
                {
                    if (op == BISHOP || op == QUEEN || (op == KING && nextto) || (op == PAWN && nextto && ((state & S2MMASK) ? (diagonaloffset[i] < 0) : (diagonaloffset[i] > 0))))
                    {
                        cheapest = materialvalue[op];
                        cheapest_from = from;
                        break;
                    }
                }
            }
            nextto = false;
        } while (isEmpty(from));
    }

    for (i = 0; i < 4; i++)
    {
        from = to;
        nextto = true;
        do
        {
            from += orthogonaloffset[i];
            if (isOpponent(from))
            {
                PieceType op = Piece(from);
                if (materialvalue[op] < cheapest)
                {
                    if (op == ROOK || op == QUEEN || (op == KING && nextto))
                    {
                        cheapest = materialvalue[op];
                        cheapest_from = from;
                        break;
                    }
                }
            }
            nextto = false;
        } while (isEmpty(from));
    }

    if (cheapest_from & 0x88)
    {
        v = 0;
    }
    else
    {
        PieceCode capture = board[to];
        int material = materialvalue[Piece(to)];
        simplePlay(cheapest_from, to);
        v = max(0, material - see(to));
        simpleUnplay(cheapest_from, to, capture);
    }
    state ^= S2MMASK;
    return v;
}


int chessposition::see(int from, int to)
{
    int v;
    state ^= S2MMASK;
    PieceCode capture = board[to];
    int material = materialvalue[Piece(to)];
    simplePlay(from, to);
    v = material - see(to);
    simpleUnplay(from, to, capture);
    state ^= S2MMASK;
    return v;
}

/* Value of the position from whites pov */
int chessposition::getPositionValue()
{
    int ph = phase();
    int result = 0;
    int firstpawn[2][10] = { 0 };
    int lastpawn[2][10] = { 0 };
    int i;
    //printf("Phase=%d\n", ph);

    for (int f = 0; f < 8; f++)
    {
        int pawnsonfile[2] = { 0,0 };
        for (int r = 0; r < 8; r++)
        {
            i = (r << 4) | f;
            if (Piece(i) == PAWN)
            {
                int col = board[i] & S2MMASK;
                if (++pawnsonfile[col] > 1)
                    // double pawn penalty
                    result += (col ? -30 : 30);
                if (col == 1 || !lastpawn[col][f + 1])
                    lastpawn[col][f + 1] = r;
                if (col == 0 || !firstpawn[col][f + 1])
                    firstpawn[col][f + 1] = r;
            }
        }
        for (int r = 0; r < 8; r++)
        {
            i = (r << 4) | f;
            if (board[i] != BLANK)
            {
                PieceType pt = Piece(i);
                int col = board[i] & S2MMASK;
                int index = i | (ph << 7) | (pt << 15) | (col << 18);

                //printf("Phase=%d; Value for %c on field %c%c: %d\n", ph, PieceChar(board[i]), 'a'+(i & 0x7), '1'+(i >> 4), *(positionvaluetable + index));
                result += *(positionvaluetable + index);
                if (pt == ROOK && (firstpawn[col][f + 1] == 0 || ((col && (firstpawn[col][f + 1] > r)) || (!col && (firstpawn[col][f + 1] < r)))))
                    // ROOK on free file
                    result += (col ? -30 : 30);

            }
        }
    }
    for (int f = 0; f < 8; f++)
    {
        for (int col = 0; col < 2; col++)
        {
            int opcol = 1 - col;
            int factor = (col ? -1 : 1);
            int pawnrank = firstpawn[col][f + 1];
            if (pawnrank)
            {
                // check for passed pawn
                if ((!lastpawn[opcol][f] || factor * lastpawn[opcol][f] <= factor * pawnrank)
                    && (!lastpawn[opcol][f + 1] || factor * lastpawn[opcol][f + 1] <= factor * pawnrank)
                    && (!lastpawn[opcol][f + 2] || factor * lastpawn[opcol][f + 2] <= factor * pawnrank))
                    result += (factor * 40);
            }
            if (pawnrank && !firstpawn[col][f] && !firstpawn[col][f + 2])
                // isolated pawn
                result -= (factor * 30);

        }
    }

    return result;
}


int chessposition::getValue()
{
    // Check for insufficient material using simnple heuristic from chessprogramming site
    if (piecenum[WPAWN] == 0 && piecenum[BPAWN] == 0)
    {
        if (piecenum[WQUEEN] == 0 && piecenum[BQUEEN] == 0 && piecenum[WROOK] == 0 && piecenum[BROOK] == 0)
        {
            if (piecenum[WBISHOP] + piecenum[WKNIGHT] <= 2
                && piecenum[BBISHOP] + piecenum[BKNIGHT] <= 2)
            {
                bool winpossible = false;
                // two bishop win if opponent has none
                if (abs(piecenum[WBISHOP] - piecenum[BBISHOP]) == 2)
                    winpossible = true;
                // bishop and knight win against bare king
                if (piecenum[WBISHOP] * piecenum[WKNIGHT] > piecenum[BBISHOP] + piecenum[BKNIGHT]
                    || piecenum[BBISHOP] * piecenum[BKNIGHT] > piecenum[WBISHOP] + piecenum[WKNIGHT])
                    winpossible = true;

                if (!winpossible)
                    return SCOREDRAW;
            }
        }
    }

    int materialVal = value;
    int positionVal = getPositionValue();
    //printf("(getValue) Materialwert: %d   Positionswert: %d\n", materialVal, positionVal);
    return materialVal + positionVal;
}


/* test the actualmove for three-fold-repetition as the repetition table may give false positive due to table collisions */
bool chessposition::testRepetiton()
{
    //chessposition oldp = *this;
    unsigned long long h = hash;
    chessmovelist ml = actualpath;
    int hit = 0;
    for (int i = ml.length - 1; i >= 0; i--)
    {
        if (ml.move[i].code == 0)
            unplayNullMove();
        else
            unplayMove(&ml.move[i]);
        if (hash == h)
            hit++;
    }
    for (int i = 0; i < ml.length; i++)
    {
        if (ml.move[i].code == 0)
        {
            playNullMove();
        }
        else
        {
            if (!playMove(&ml.move[i]))
            {
                printf("Alarm. Wie kommt ein illegaler Zug %s (%d) in die actuallist\n", ml.move[i].toString().c_str(), i);
                ml.print();
            }
        }
    }
    if (h != hash)
    {
        printf("Alarm! testRepetitin landet bei falschem Hash-Wert.\n");
        //oldp.print();
        print();
    }

    //print();
    return (hit >= 2);
}
#endif


engine::engine()
{
    // Allocate all needed objects and connect them
    pos = new chessposition();
    rp = new repetition();
    pos->rp = rp;
    tp = new transposition();
    pos->tp = tp;
    tp->pos = pos;
#ifdef BITBOARD
	initBitmaphelper();
#endif

    setOption("hash", "150");

#ifdef _WIN32
    LARGE_INTEGER f;
    QueryPerformanceFrequency(&f);
    frequency = f.QuadPart;
#else
    frequency = 1000000000LL;
#endif

}

engine::~engine()
{
    delete pos;
    delete rp;
    delete tp;
#ifdef BITBOARD
#endif
}


int engine::getScoreFromEnginePoV()
{
	return (isWhite ? pos->getValue() : -pos->getValue());
}

void engine::setOption(string sName, string sValue)
{
    bool resetTp = false;
    int newint;
	transform(sName.begin(), sName.end(), sName.begin(), ::tolower);
	transform(sValue.begin(), sValue.end(), sValue.begin(), ::tolower);
    if (sName == "clear hash")
        pos->tp->clean();
    if (sName == "hash")
    {
        newint = stoi(sValue);
        if (newint < 1)
            // at least a small hash table is required
            return;
        if (sizeOfTp != newint)
        {
            sizeOfTp = newint;
            resetTp = true;
        }
    }
    if (resetTp)
    {
        pos->tp->setSize(sizeOfTp);
    }
}

void engine::communicate(string inputstring)
{
    string fen;
    vector<string> moves;
    vector<string> searchmoves;
    vector<string> commandargs;
    GuiToken command;
    size_t ci, cs;
	bool bGetName, bGetValue;
	string sName, sValue;
	bool bMoves;
    thread *searchthread = NULL;
    do
    {
        commandargs.clear();
        command = myUci->parse(&commandargs, inputstring);
        ci = 0;
        cs = commandargs.size();
        switch (command)
        {
		case UCIDEBUG:
			if (ci < cs)
			{
                if (commandargs[ci] == "on")
                    debug = true;
                else if (commandargs[ci] == "off")
                    debug = false;
                else if (commandargs[ci] == "this")
                    pos->debughash = pos->hash;
			}
            break;
        case UCI:
            myUci->send("id name %s\n", name);
            myUci->send("id author %s\n", author);
            myUci->send("option name Clear Hash type button\n");
            myUci->send("option name Hash type spin default 150 min 1 max 1048576\n");
            myUci->send("uciok\n", author);
            break;
		case SETOPTION:
            if (searchthread)
            {
                myUci->send("info string Changing option while searching is not supported.\n");
                break;
            }
			bGetName = bGetValue = false;
			sName = sValue = "";
			while (ci < cs)
			{
				if (commandargs[ci] == "name")
				{
					setOption(sName, sValue);
					bGetName = true;
					bGetValue = false;
					sName = "";
				} else if (commandargs[ci] == "value")
				{
					bGetValue = true;
					bGetName = false;
					sValue = "";
				} else if (bGetName)
				{
					if (sName != "")
						sName += " ";
					sName += commandargs[ci];
				} else if (bGetValue)
				{
					if (sValue != "")
						sValue += " ";
					sValue += commandargs[ci];
				}
				ci++;
			}
			setOption(sName, sValue);
			break;
        case ISREADY:
            myUci->send("readyok\n");
            break;
        case POSITION:
            if (cs == 0)
                break;
            bMoves = false;
			moves.clear();
            fen = "";

			if (commandargs[ci] == "startpos")
            {
                ci++;
                fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
            }
            else if (commandargs[ci] == "fen")
            {
                while (++ci < cs && commandargs[ci] != "moves")
                    fen = fen + commandargs[ci] + " ";
            }
            while (ci < cs)
            {
                if (commandargs[ci] == "moves")
                {
                    bMoves = true;
                }
                else if (bMoves)
                {
                    moves.push_back(commandargs[ci]);
                }
                ci++;
            }
            if (fen == "")
                break;
            pos->getFromFen(fen.c_str());
            for (vector<string>::iterator it = moves.begin(); it != moves.end(); ++it)
            {
                if (!pos->applyMove(*it))
					printf("info string Alarm! Zug %s nicht anwendbar (oder Enginefehler)\n", (*it).c_str());
            }
            pos->ply = 0;

            if (debug)
            {
                pos->print();
            }
            break;
        case GO:
			searchmoves.clear();
			wtime = btime = winc = binc = movestogo = mate = maxdepth = 0;
            infinite = false;
            while (ci < cs)
            {
                if (commandargs[ci] == "searchmoves")
                {
                    while (++ci < cs && AlgebraicToIndex(commandargs[ci], 0x88) != 0x88 && AlgebraicToIndex(&commandargs[ci][2], 0x88) != 0x88)
                        searchmoves.push_back(commandargs[ci]);
                }

                else if (commandargs[ci] == "wtime")
                {
                    if (++ci < cs)
                        wtime = stoi(commandargs[ci++]);
                }
                else if (commandargs[ci] == "btime")
                {
                    if (++ci < cs)
                        btime = stoi(commandargs[ci++]);
                }
                else if (commandargs[ci] == "winc")
                {
                    if (++ci < cs)
                        winc = stoi(commandargs[ci++]);
                }
                else if (commandargs[ci] == "binc")
                {
                    if (++ci < cs)
                        binc = stoi(commandargs[ci++]);
                }
                else if (commandargs[ci] == "movetime")
                {
                    movestogo = 1;
                    winc = binc = 0;
                    if (++ci < cs)
                        wtime = btime = stoi(commandargs[ci++]);
                }
                else if (commandargs[ci] == "movestogo")
				{
					if (++ci < cs)
						movestogo = stoi(commandargs[ci++]);
				}
				else if (commandargs[ci] == "mate")
				{
					if (++ci < cs)
						mate = stoi(commandargs[ci++]);
				}
                else if (commandargs[ci] == "depth")
                {
                    if (++ci < cs)
                        maxdepth = stoi(commandargs[ci++]);
                }
                else if (commandargs[ci] == "infinite")
                {
                    infinite = true;
                    ci++;
                }
                else
                    ci++;
            }
            isWhite = (pos->w2m());
            searchthread = new thread(&searchguide, this);
            if (inputstring != "")
            {
                // bench mode; wait for end of search
                searchthread->join();
                delete searchthread;
                searchthread = nullptr;
            }
            break;
		case STOP:
        case QUIT:
			stopLevel = ENGINESTOPIMMEDIATELY;
            if (searchthread && searchthread->joinable())
            {
                searchthread->join();
                delete searchthread;
                searchthread = nullptr;
            }
            break;
        default:
            break;
		}
	} while (command != QUIT && inputstring == "");
}

    