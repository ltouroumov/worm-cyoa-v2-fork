import json

NETWORK_SCORE_ENTRY = {
    "afterText": "Network Capacity",
    "beforeText": "Cost:",
    "id": "1u",
    "requireds": [
    {
        "afterText": "",
        "beforeText": "Required:",
        "id": "",
        "operator": "",
        "orRequired": [
        {
            "req": ""
        },
        {
            "req": ""
        },
        {
            "req": ""
        },
        {
            "req": ""
        }
        ],
        "reqId": "k89b",
        "reqId1": "",
        "reqId2": "",
        "reqId3": "",
        "reqPoints": 0,
        "required": True,
        "requireds": [],
        "showRequired": True,
        "type": "id"
    }
    ],
    "showScore": True,
    "type": "",
    "value": "1"
}

POWERS_ROWS = {
    "io2d", # Tier 3 Powers
    "jsch", # Power Copy
    "zg2f", # Tier 2 Powers
    "e018", # Tier 1 Powers
}
SP_SCORE = "rm"
NET_SCORE = "1u"

def has_score(obj, score_id):
    return any(score['id'] == score_id for score in obj['scores'])
    
def add_network_cost(obj):
    obj['scores'].append(NETWORK_SCORE_ENTRY)

if __name__ == '__main__':
    with open('project-v12.json', mode='r') as fd:
        project = json.load(fd)

    big_images = []
    total_image_bytes = 0
    for row in project['rows']:
        if row['id'] not in POWERS_ROWS:
            continue

        print(f"Processing Row {row['title']} ({row['id']})")

        for obj in row['objects']:
            if has_score(obj, SP_SCORE) and not has_score(obj, NET_SCORE):
                add_network_cost(obj)
                print(f"Added Network Cost to {obj['title']} ({obj['id']})")

    with open('project-v12.json', mode='w+') as fd:
        json.dump(project, fd)
