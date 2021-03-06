# Generated by Django 2.0.1 on 2018-01-17 00:03

from django.db import migrations, models
import django.db.models.deletion


class Migration(migrations.Migration):

    dependencies = [
        ('main', '0007_testfailure_pretty'),
    ]

    operations = [
        migrations.CreateModel(
            name='Opcode',
            fields=[
                ('id', models.AutoField(auto_created=True, primary_key=True, serialize=False, verbose_name='ID')),
                ('name', models.CharField(max_length=128)),
                ('arch', models.ForeignKey(on_delete=django.db.models.deletion.CASCADE, to='main.Arch')),
            ],
        ),
        migrations.AlterField(
            model_name='testfailure',
            name='opcode',
            field=models.ForeignKey(on_delete=django.db.models.deletion.CASCADE, to='main.Opcode'),
        ),
        migrations.AlterField(
            model_name='testsuccess',
            name='opcode',
            field=models.ForeignKey(on_delete=django.db.models.deletion.CASCADE, to='main.Opcode'),
        ),
    ]
