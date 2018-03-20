#!/usr/bin/env groovy

pipeline {
    agent any
    stages {
        stage('Build & Test') {
            steps {
                withDockerContainer('kyroy/zokrates-test') {
                    sh 'RUSTFLAGS="-D warnings" cargo build'
                    sh 'RUSTFLAGS="-D warnings" cargo test'
                }
            }
        }

        stage('Docker Build & Push') {
            when {
                environment name: 'BRANCH_NAME', value: 'master'
            }
            steps {
                script {
                    def dockerImage = docker.build("kyroy/zokrates")
                    docker.withRegistry('https://registry.hub.docker.com', 'dockerhub-kyroy') {
                        dockerImage.push("latest")
                    }
                }
            }
        }
    }
    post {
        always {
            // junit allowEmptyResults: true, testResults: '*test.xml'
            deleteDir()
        }
        changed {
            notifyStatusChange notificationRecipients: 'mail@kyroy.com', componentName: 'ZoKrates'
        }
    }
}
