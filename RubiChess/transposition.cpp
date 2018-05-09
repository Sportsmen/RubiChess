
#include "RubiChess.h"


/* A small noncryptographic PRNG */
/* http://www.burtleburtle.net/bob/rand/smallprng.html */

u8 ranval(ranctx *x) {
    u8 e = x->a - rot(x->b, 7);
    x->a = x->b ^ rot(x->c, 13);
    x->b = x->c + rot(x->d, 37);
    x->c = x->d + e;
    x->d = e + x->a;
    return x->d;
}

void raninit(ranctx *x, u8 seed) {
    u8 i;
    x->a = 0xf1ea5eed, x->b = x->c = x->d = seed;
    for (i = 0; i<20; ++i) {
        (void)ranval(x);
    }
}

zobrist::zobrist()
{
    raninit(&rnd, 0);
    int i;
    int j = 0;
    for (i = 0; i < 128 * 16; i++)
    {
        unsigned long long r = getRnd();
#ifdef BITBOARD
        // make the boardtable and so the hash compatible with older 0x88-board representation
        if (!((i >> 4) & 0x88))
            boardtable[j++] = r;
#else
        boardtable[j++] = r;
#endif
    }
#ifdef BITBOARD
    // make hashing simpler but stay compatible to board88
    unsigned long long castle[4];
    unsigned long long ep[8];
    for (i = 0; i < 4; i++)
        castle[i] = getRnd();
    for (i = 0; i < 8; i++)
        ep[i] = getRnd();
    for (i = 0; i < 32; i++)
    {
        cstl[i] = 0ULL;
        for (j = 0; j < 4; j++)
        {
            if (i & (1 << (j+1)))
                cstl[i] ^= castle[j];
        }
    }
    for (i = 0; i < 64; i++)
    {
        ept[i] = 0ULL;
        if (RANK(i) == 2 || RANK(i) == 5)
            ept[i] = ep[FILE(i)];
    }

#else
    for (i = 0; i < 4; i++)
        castle[i] = getRnd();
    for (i = 0; i < 8; i++)
        ep[i] = getRnd();
#endif
    s2m = getRnd();
}

unsigned long long zobrist::getRnd()
{
    return ranval(&rnd);
}


u8 zobrist::modHash(int i)
{
    return 0;
}

#ifdef BITBOARD

u8 zobrist::getHash()
{
    u8 hash = 0;
    int i;
    int state = pos.state;
    for (i = WPAWN; i <= BKING; i++)
    {
        U64 pmask = pos.piece00[i];
        unsigned int index;
        while (LSB(index, pmask))
        {
            hash ^= boardtable[(index << 4) | i];
            pmask ^= (1ULL << index);
        }
    }

    if (state & S2MMASK)
        hash ^= s2m;

    hash ^= cstl[state & CASTLEMASK];
    hash ^= ept[pos.ept];

    return hash;
}

u8 zobrist::getPawnHash()
{
    u8 hash = 0;
    for (int i = WPAWN; i <= BPAWN; i++)
    {
        U64 pmask = pos.piece00[i];
        unsigned int index;
        while (LSB(index, pmask))
        {
            hash ^= boardtable[(index << 4) | i];
            pmask ^= (1ULL << index);
        }
    }

    return hash;
}

#else
u8 zobrist::getHash()
{
    u8 hash = 0;
    int i;
    int state = pos.state;
    for (i = 0; i < 120; i++)
    {
        if (!(i & 0x88) && pos.mailbox[i] != BLANK)
        {
            hash ^= boardtable[(i << 4)  | pos.mailbox[i]];
        }
    }
    if (state & S2MMASK)
        hash ^= s2m;
    state >>= 1;

    for (i = 0; i < 4; i++)
    {
        if (state & 1)
            hash ^= castle[i];
        state >>= 1;
    }

    if (pos.ept)
        hash ^= ep[pos.ept & 0x7];

    return hash;
}


u8 zobrist::getPawnHash()
{
    u8 hash = 0;
    int i;
    for (i = 0; i < 120; i++)
    {
        if (!(i & 0x88) && (pos.mailbox[i] >> 1) == PAWN)
        {
            hash ^= boardtable[(i << 4) | pos.mailbox[i]];
        }
    }

    return hash;
}

#endif


u8 zobrist::getMaterialHash()
{
    u8 hash = 0;
    for (PieceCode pc = WPAWN; pc <= BKING; pc++)
    {
        int count = 0;
        for (int j = 0; j < BOARDSIZE; j++)
        {
#ifndef BITBOARD
            if (!(j & 0x88))
#endif
                if (pos.mailbox[j] == pc)
                    hash ^= zb.boardtable[(count++ << 4) | pc];
        }
    }
    return hash;
}


transposition::~transposition()
{
    if (size > 0)
        delete table;
}

int transposition::setSize(int sizeMb)
{
    int restMb = 0;
    int msb = 0;
    if (size > 0)
        delete table;
    U64 maxsize = ((U64)sizeMb << 20) / sizeof(transpositioncluster);
    if (MSB(msb, maxsize))
    {
        size = (1ULL << msb);
        restMb = (int)(((maxsize ^ size) >> 20) * sizeof(transpositioncluster));  // return rest for pawnhash
    }

    sizemask = size - 1;
    table = (transpositioncluster*)malloc((size_t)(size * sizeof(transpositioncluster)));
    clean();
    return restMb;
}

void transposition::clean()
{
    memset(table, 0, (size_t)(size * sizeof(transpositioncluster)));
    used = 0;
    numofsearchShiftTwo = 0xfc; // 0x3f << 2; will be incremented / reset to 0 before first search
}


unsigned int transposition::getUsedinPermill()
{
    if (size > 0)
        return (unsigned int) (used * 1000 / size / BUCKETSINTABLE);
    else
        return 0;
}


void transposition::addHash(transpositionentry* entry, int val, int statval, int bound, int depth, uint32_t move)
{
    unsigned long long hash = pos.hash;

    if (entry->hashupper == 0)
        used++;
    entry->hashupper = (uint32_t)(hash >> 32);
    entry->depth = (unsigned char)depth;
    if (MATEFORME(val))
        val += pos.ply;
    else if (MATEFOROPPONENT(val))
        val -= pos.ply;
    entry->value = (short)val;
	entry->staticValue = (short)statval;
    entry->boundAndAge = (unsigned char)(bound | numofsearchShiftTwo);
    entry->movecode = (move & 0xffff);
}


void transposition::printHashentry()
{
    unsigned long long hash = pos.hash;
    transpositioncluster *tc = &table[hash & sizemask];

    printf("Hashentry for %llx\n", hash);
    for (int i = 0; i < BUCKETSINTABLE; i++)
    {
        transpositionentry *entry = &tc->entry[i];
        if ((entry->hashupper) == (hash >> 32))
        {
            printf("Match in upper part: %x / %x\n", (unsigned int)entry->hashupper, (unsigned int)(hash >> 32));
            printf("Move code: %x\n", (unsigned int)entry->movecode);
            printf("Depth:     %d\n", entry->depth);
            printf("Value:     %d\n", entry->value);
            printf("BoundType: %d\n", entry->boundAndAge & BOUNDMASK);
            return;
        }

    }
    printf("No match!!!\n");
}

void transposition::preFetch(unsigned long long h)
{
	_mm_prefetch((char*)&table[h & sizemask], _MM_HINT_T0);
}


// return the tp entry of the current position or an empty bucket or the oldest bucket
transpositionentry* transposition::probeHash(bool *found)
{
#ifdef EVALTUNE
    // don't use transposition table when tuning evaluation
    *found = false;
    return nullptr;
#endif
    unsigned long long hash = pos.hash;
    transpositioncluster *tc = &table[hash & sizemask];

    for (int i = 0; i < BUCKETSINTABLE; i++)
    {
        transpositionentry *entry = &tc->entry[i];
        if (!entry->hashupper || (entry->hashupper) == (hash >> 32))
        {
            *found = (bool)entry->hashupper;
            if (*found && (entry->boundAndAge & 0xfc) != numofsearchShiftTwo)
                entry->boundAndAge = (entry->boundAndAge & BOUNDMASK) | numofsearchShiftTwo;
            
			return entry;
        }
    }
    // All buckets are in use; search for least valuable
    // shameless copy of SF replacement formular
    int iLeastValuable = 0;
    for (int i = 1; i < BUCKETSINTABLE; i++)
    {
        if ((tc->entry[i].depth - (259 + numofsearchShiftTwo - TPGETAGE(tc->entry[i])) * 1)
            < (tc->entry[iLeastValuable].depth - (259 + numofsearchShiftTwo - TPGETAGE(tc->entry[iLeastValuable])) * 1))
        {
            iLeastValuable = i;
        }
    }
    *found = false;
    return &tc->entry[iLeastValuable];
}


bool transposition::testHashValue(transpositionentry *entry, int alpha, int beta, int *value)
{
    *value = entry->value;
    char flag = PTPGETBOUND(entry);
    if (MATEFORME(*value))
        *value -= pos.ply;
    else if (MATEFOROPPONENT(*value))
        *value += pos.ply;
    if (flag == HASHEXACT)
    {
        return true;
    }
    else if (flag == HASHALPHA && *value <= alpha)
    {
        *value = alpha;
        return true;
    }
    else if (flag == HASHBETA && *value >= beta)
    {
        *value = beta;
        return true;
    }

    return false;
}



pawnhash::~pawnhash()
{
    if (size > 0)
        delete table;
}

void pawnhash::setSize(int sizeMb)
{
    int msb = 0;
    if (size > 0)
        delete table;
    size = ((U64)sizeMb << 20) / sizeof(S_PAWNHASHENTRY);
    if (MSB(msb, size))
        size = (1ULL << msb);

    sizemask = size - 1;
    table = (S_PAWNHASHENTRY*)malloc((size_t)(size * sizeof(S_PAWNHASHENTRY)));
    clean();
}

void pawnhash::clean()
{
    memset(table, 0, (size_t)(size * sizeof(S_PAWNHASHENTRY)));
#ifdef DEBUG
    used = 0;
    hit = 0;
    query = 0;
#endif
}

bool pawnhash::probeHash(pawnhashentry **entry)
{
    unsigned long long hash = pos->pawnhash;
    unsigned long long index = hash & sizemask;
    *entry = &table[index];
#ifdef DEBUG
    query++;
#endif
    if (((*entry)->hashupper) == (hash >> 32))
    {
#ifdef DEBUG
        hit++;
#endif
#ifdef EVALTUNE
        // don't use pawn hash when tuning evaluation
        return false;
#endif
        return true;
    }
    (*entry)->hashupper = (uint32_t)(hash >> 32);
    return false;
}

unsigned int pawnhash::getUsedinPermill()
{
#ifdef DEBUG
    if (size > 0)
        return (unsigned int)(used * 1000 / size);
    else
        return 0;
#else
    return 0;
#endif
}


void repetition::clean()
{
    memset(table, 0, 0x10000);
}

void repetition::addPosition(unsigned long long hash)
{
    table[hash & 0xffff]++;
}

void repetition::removePosition(unsigned long long hash)
{
    table[hash & 0xffff]--;
}

int repetition::getPositionCount(unsigned long long hash)
{
    return table[hash & 0xffff];
}

repetition rp;
transposition tp;
pawnhash pwnhsh;
