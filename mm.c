/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* Basic constants and macros */
#define WSIZE 4             // 워드, 헤더, 푸터 사이즈 (단위: 바이트)
#define DSIZE 8             // 더블 워드 사이즈 (단위: 바이트)
#define CHUNKSIZE (1 << 12) // 힙을 이만큼 늘림 (단위: 바이트)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/*  하나의 워드에 메모리 블록의 크기와 할당 상태를 함께 저장 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p에 있는 워드를 읽고 쓰기 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p에 있는 워드에서 메모리 블록의 크기와 할당 상태 읽기 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 주어진 블록 포인터 bp에 대해서, 헤더와 푸터의 주소를 구한다 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 주어진 블록 포인터 bp에 대해서, 다음 블록과 이전 블록의 위치를 구한다 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/////////////// 전방 선언 /////////////////

static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
void *mm_realloc(void *ptr, size_t size);

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 8바이트 정렬을 유지하기 위해 짝수인 워드로만 할당한다 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    /* mem_sbrk로 힙의 brk 포인터를 변경 시도. 만약 불가능하면 NULL 반환. */
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 가용 블록 헤더/푸터, 에필로그 푸터를 초기화 */
    /* sbrk에서 반환된 포인터 bp는 이전의 에필로그 블록을 가리키고 있음.
       sbrk로 heap의 크기가 늘어났으므로, 이전의 에필로그 블록을 가용 블록으로 변환해야 함.
       이를 위해 새로운 가용 블록의 헤더와 푸터를 설정하고, 새로운 에필로그 블록을 생성하는 과정. */
    PUT(HDRP(bp), PACK(size, 0));         // 가용 블록 헤더
    PUT(FTRP(bp), PACK(size, 0));         // 가용 블록 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더

    // 이전 에필로그 블록이 가용 블록이었다면, 새로운 힙 영역의 가용 블록과 결합함
    return coalesce(bp);
}

/*
 * mm_init - initialize the malloc package.
 */

static char *heap_listp;

int mm_init(void)
{
    // char *heap_listp = NULL;
    /* 빈 heap 생성 */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            // 정렬 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 헤더
    heap_listp += (2 * WSIZE);

    /* CHUNKSIZE 바이트의 가용 블록만큼 heap 영역을 늘림 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      // 조정된 블록 사이즈
    size_t extendsize; // 힙이 부족하면 늘려야 하는 양
    char *bp;

    // 이상한 요청 무시
    if (size == 0)
        return NULL;

    // 넣을 데이터의 사이즈가 더블 워드보다 작으면,
    // 할당할 블록의 크기를 강제로 키워준다
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    // 아니라면 8바이트 정렬만 맞춰준다
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 알맞는 가용 블록 찾기
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    // 맞는 가용 블록이 없으면 힙 공간을 추가하고 블록 넣기
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize)
{
    void *bp = heap_listp;

    // 힙의 데이터가 시작되는 영역부터 시작해서 에필로그 블록까지 탐색
    while (GET_SIZE(HDRP(bp)) > 0)
    {
        // 헤더를 봤더니 할당되어 있지 않고, 충분히 크다면
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp; // 할당

        bp = NEXT_BLKP(bp);
    }
    return NULL; // 맞는 블록이 없으면 NULL 반환
}

static void place(void *bp, size_t asize)
{

    if ((GET_SIZE(HDRP(bp)) - asize) >= (2 * DSIZE))
    {
        PUT(bp + asize - DSIZE, PACK(asize, 1));                      // 새 푸터에 정보 넣기
        PUT(bp + asize - WSIZE, PACK(GET_SIZE(HDRP(bp)) - asize, 0)); // 새 헤더에 정보 넣기
        PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)) - asize, 0));           // 원래 푸터의 정보 갱신
        PUT(HDRP(bp), PACK(asize, 1));                                // 원래 헤더의 정보 갱신
    }
    else
    {
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
        PUT(FTRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
    }
}

/*
 * mm_free - 헤더와 푸터는 그대로지만 가용인지 아닌지 상태만 바꿈
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

// coalesce - 가용 블록들을 병합시키는 함수

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 : 이전과 다음 블록이 모두 할당되어 있다. 병합 불가
    if (prev_alloc && next_alloc)
    {
        return bp;
    }

    // case 2 : 다음 블록만 가용 블록. 다음 블록과 병합.
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // 헤더에 기록된 size를 바꾼다
        PUT(FTRP(bp), PACK(size, 0)); // 헤더에 기록된 size가 바뀌었으니 FTRP(bp)의 반환값도 size만큼 커진다
    }

    // case 3 : 이전 블록만 가용 블록. 이전 블록과 병합.
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));            // 푸터에 기록된 size를 바꾼다
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 가용 블록의 헤더에 기록된 size를 바꾼다
        bp = PREV_BLKP(bp);
    }

    // case 4 : 이전 블록과 다음 블록 모두 가용 블록. 모두 병합.
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 가용 블록의 헤더에 기록된 size를 바꾼다
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // (bp에 적힌 size는 아직 바뀌지 않았으니 NEXT_BLKP가 원하는대로 작동)
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    // 새로 할당할 size에 맞는 가용 블록 찾아서 할당
    newptr = mm_malloc(size);
    // size가 0이거나 음수이면 NULL 반환
    if (newptr == NULL)
        return NULL;

    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    // 책과 repo 코드의 로직이 달라서 문제가 생긴다. 고쳐줘야 함.

    // copy할 size를 oldptr에 역참조한 값에서 추출
    copySize = GET_SIZE(HDRP(oldptr));

    // 재할당하려는 블록의 크기가 기존 블록의 크기보다 작을 경우,
    // 실제로 복사할 크기를 size로 제한
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}