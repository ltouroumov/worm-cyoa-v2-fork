<div class="object-wrapper">
<onlyinclude>
<div class="object">
<h2>[[{{ page_name }}|{{ obj.title }}]]</h2>
{% if obj.imageLink -%}
<div class="image">
<htmltag tagname="img" src="{{ obj.imageLink }}" width="100%"/>
</div>
{% endif -%}
<div class="text">{{ obj.text }}</div>
</div>
</onlyinclude>
{% for addon in obj.addons -%}
<div class="addon">
<h3>{{ addon.title }}</h3>
<div class="text">{{ addon.text }}</div>
</div>
{% endfor -%}
</div>