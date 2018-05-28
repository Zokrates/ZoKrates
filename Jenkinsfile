#!/usr/bin/env groovy

pipeline {
    agent any
    stages {
        stage('Build') {
            steps {
                withDockerContainer('kyroy/zokrates-test') {
                    sh 'RUSTFLAGS="-D warnings" cargo build'
                }
            }
        }

        stage('Test') {
            steps {
                withDockerContainer('kyroy/zokrates-test') {
                    sh 'RUSTFLAGS="-D warnings" cargo test'
                }
            }
        }

        stage('Integration Test') {
            when {
                expression { env.BRANCH_NAME == 'master' || env.BRANCH_NAME == 'develop' }
            }
            steps {
                withDockerContainer('kyroy/zokrates-test') {
                    sh 'RUSTFLAGS="-D warnings" cargo test -- --ignored'
                }
            }
        }

        stage('Docker Build & Push') {
            when {
                expression { env.BRANCH_NAME == 'master' }
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
